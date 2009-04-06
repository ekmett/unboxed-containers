{-# LANGUAGE TypeFamilies, CPP, ViewPatterns, MagicHash, UnboxedTuples, PatternGuards #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

{------------------------------------------------------------------------------
-- |
-- Module      :  Data.Set.Unboxed
-- Copyright   :  (c) Edward Kmett 2009
--                (c) Daan Leijen 2002
-- License     :  BSD3
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (type families, view patterns, unboxed tuples)
--
-- An efficient implementation of sets.
--
-- Since many function names (but not the type name) clash with
-- "Prelude" names, this module is usually imported @qualified@, e.g.
--
-- >  import Data.Set.Unboxed (USet)
-- >  import qualified Data.Set.Unboxed as USet
--
-- The implementation of 'USet' is based on /size balanced/ binary trees (or
-- trees of /bounded balance/) as described by:
--
--    * Stephen Adams, \"/Efficient sets: a balancing act/\",
--  Journal of Functional Programming 3(4):553-562, October 1993,
--  <http://www.swiss.ai.mit.edu/~adams/BB/>.
--
--    * J. Nievergelt and E.M. Reingold,
--  \"/Binary search trees of bounded balance/\",
--  SIAM journal of computing 2(1), March 1973.
--
-- Note that the implementation is /left-biased/ -- the elements of a
-- first argument are always preferred to the second, for example in
-- 'union' or 'insert'.  Of course, left-biasing can only be observed
-- when equality is an equivalence relation instead of structural
-- equality.
--
-- Modified from "Data.Set" to use type families for automatic unboxing
-----------------------------------------------------------------------------
-}

module Data.Set.Unboxed ( 
            -- * Set type
              USet          -- instance Eq,Ord,Show,Read,Data,Typeable
            , US
            , Boxed(Boxed)

            -- * Operators
            , (\\)

            -- * Query
            , null
            , size
            , member
            , notMember
            , isSubsetOf
            , isProperSubsetOf
            
            -- * Construction
            , empty
            , singleton
            , insert
            , delete
            
            -- * Combine
            , union, unions
            , difference
            , intersection
            
            -- * Filter
            , filter
            , partition
            , split
            , splitMember

            -- * Map
            , map
            , mapMonotonic

            -- * Fold
            , fold

            -- * Min\/Max
            , findMin
            , findMax
            , deleteMin
            , deleteMax
            , deleteFindMin
            , deleteFindMax
            , maxView
            , minView

            -- * Conversion

            -- ** List
            , elems
            , toList
            , fromList
            
            -- ** Ordered list
            , toAscList
            , fromAscList
            , fromDistinctAscList
                        
            -- * Debugging
            , showTree
            , showTreeWith
            , valid
            ) where

import Prelude hiding (filter,foldr,null,map)
import qualified Data.List as List
import Data.Monoid (Monoid(..))
import Data.Word
import Data.Int

{-
-- just for testing
import Test.QuickCheck 
import Data.List (nub,sort)
import qualified Data.List as List
-}

#if __GLASGOW_HASKELL__
import Text.Read
#endif

{--------------------------------------------------------------------
  Operators
--------------------------------------------------------------------}
infixl 9 \\ --

-- | /O(n+m)/. See 'difference'.
(\\) :: (US a, Ord a) => USet a -> USet a -> USet a
m1 \\ m2 = difference m1 m2

{--------------------------------------------------------------------
  Sets are size balanced trees
--------------------------------------------------------------------}
type Size     = Int

-- | A set of values @a@.
data Set a    = Tip 
              | Bin {-# UNPACK #-} !Size !a !(USet a) !(USet a) 

-- smart unboxed types
class US a where
    data USet a

    -- | Extract and rebox the specialized node format
    view :: USet a -> Set a

    -- | Apply the view to tip and bin continuations
    viewk :: b -> (Size -> a -> USet a -> USet a -> b) -> USet a -> b
    viewk f k x = case view x of
        Bin s i l r -> k s i l r
        Tip -> f

    -- | View just the value and left and right child of a bin
    viewBin :: USet a -> (# a, USet a, USet a #)
    viewBin x = case view x of 
        Bin _ i l r -> (# i, l, r #)
        Tip -> error "viewBin"

    -- | /O(1)/. The number of elements in the set.
    size :: USet a -> Size
    size = viewk 0 size' where 
        size' s _ _ _ = s

    -- | /O(1)/. Is this the empty set?
    null :: USet a -> Bool

    -- | Smart tip constructor
    tip :: USet a

    -- | Smart bin constructor
    bin :: Size -> a -> USet a -> USet a -> USet a

instance (US a, Ord a) => Monoid (USet a) where
    mempty  = empty
    mappend = union
    mconcat = unions

{-
instance US a => Generator (USet a) where
    type Elem (USet a) = a
    mapReduce _ (null -> True) = mempty
    mapReduce f (view -> Bin _s k l r) = mapReduce f l `mappend` f k `mappend` mapReduce f r
-}

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}
-- | /O(log n)/. Is the element in the set?
member :: (US a, Ord a) => a -> USet a -> Bool
member x = go where
    go = viewk False (\_ y l r -> case compare x y of
            LT -> go l
            GT -> go r
            EQ -> True)

-- | /O(log n)/. Is the element not in the set?
notMember :: (US a, Ord a) => a -> USet a -> Bool
notMember x t = not $ member x t

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}
-- | /O(1)/. The empty set.
empty :: US a => USet a
empty = tip

-- | /O(1)/. Create a singleton set.
singleton :: US a => a -> USet a
singleton x = bin 1 x tip tip

{--------------------------------------------------------------------
  Insertion, Deletion
--------------------------------------------------------------------}
-- | /O(log n)/. Insert an element in a set.
-- If the set already contains an element equal to the given value,
-- it is replaced with the new value.
insert :: (US a, Ord a) => a -> USet a -> USet a
insert x = go where
    go = viewk (singleton x) (\sz y l r -> case compare x y of
        LT -> balance y (go l) r
        GT -> balance y l (go r)
        EQ -> bin sz x l r)
{-# SPECIALIZE INLINE insert :: Int -> USet Int -> USet Int #-}

-- | /O(log n)/. Delete an element from a set.
delete :: (US a, Ord a) => a -> USet a -> USet a
delete x = go where
    go = viewk tip $ \ _ y l r -> case compare x y of
        LT -> balance y (go l) r
        GT -> balance y l (go r)
        EQ -> glue l r

{--------------------------------------------------------------------
  Subset
--------------------------------------------------------------------}
-- | /O(n+m)/. Is this a proper subset? (ie. a subset but not equal).
isProperSubsetOf :: (US a, Ord a) => USet a -> USet a -> Bool
isProperSubsetOf s1 s2 = (size s1 < size s2) && (isSubsetOf s1 s2)

-- | /O(n+m)/. Is this a subset?
-- @(s1 `isSubsetOf` s2)@ tells whether @s1@ is a subset of @s2@.
isSubsetOf :: (US a, Ord a) => USet a -> USet a -> Bool
isSubsetOf t1 t2 = (size t1 <= size t2) && (isSubsetOfX t1 t2)

isSubsetOfX :: (US a, Ord a) => USet a -> USet a -> Bool
isSubsetOfX _ (null -> True)         = False
isSubsetOfX (null -> True)  _        = True
isSubsetOfX (view -> Bin _ x l r) t  = found && isSubsetOfX l lt && isSubsetOfX r gt
  where
    (lt,found,gt) = splitMember x t


{--------------------------------------------------------------------
  Minimal, Maximal
--------------------------------------------------------------------}
-- | /O(log n)/. The minimal element of a set.
findMin :: US a => USet a -> a
findMin (view -> Bin _ x (null -> True) _) = x
findMin (view -> Bin _ _ l _)   = findMin l
findMin _ = error "Set.findMin: empty set has no minimal element"

-- | /O(log n)/. The maximal element of a set.
findMax :: US a => USet a -> a
findMax (view -> Bin _ x _ (null -> True))  = x
findMax (view -> Bin _ _ _ r)    = findMax r
findMax _ = error "Set.findMax: empty set has no maximal element"

-- | /O(log n)/. Delete the minimal element.
deleteMin :: US a => USet a -> USet a
deleteMin (view -> Bin _ _ (null -> True) r) = r
deleteMin (view -> Bin _ x l r)   = balance x (deleteMin l) r
deleteMin _ = tip

-- | /O(log n)/. Delete the maximal element.
deleteMax :: US a => USet a -> USet a
deleteMax (view -> Bin _ _ l (null -> True)) = l
deleteMax (view -> Bin _ x l r)   = balance x l (deleteMax r)
deleteMax _ = tip

{--------------------------------------------------------------------
  Union. 
--------------------------------------------------------------------}
-- | The union of a list of sets: (@'unions' == 'foldl' 'union' 'empty'@).
unions :: (US a, Ord a) => [USet a] -> USet a
unions ts
  = foldlStrict union empty ts


-- | /O(n+m)/. The union of two sets, preferring the first set when
-- equal elements are encountered.
-- The implementation uses the efficient /hedge-union/ algorithm.
-- Hedge-union is more efficient on (bigset `union` smallset).
union :: (US a, Ord a) => USet a -> USet a -> USet a
union (null -> True) t2  = t2
union t1 (null -> True)  = t1
union t1 t2 = hedgeUnion (const LT) (const GT) t1 t2

hedgeUnion :: (US a, Ord a) => (a -> Ordering) -> (a -> Ordering) -> USet a -> USet a -> USet a
hedgeUnion _     _     t1 (null -> True)                    = t1
hedgeUnion cmplo cmphi (null -> True) (view -> Bin _ x l r) = join x (filterGt cmplo l) (filterLt cmphi r)
hedgeUnion cmplo cmphi (view -> Bin _ x l r) t2            = join x (hedgeUnion cmplo cmpx l (trim cmplo cmpx t2)) (hedgeUnion cmpx cmphi r (trim cmpx cmphi t2))
  where
    cmpx = compare x

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}
-- | /O(n+m)/. Difference of two sets. 
-- The implementation uses an efficient /hedge/ algorithm comparable with /hedge-union/.
difference :: (US a, Ord a) => USet a -> USet a -> USet a
difference (null -> True) _   = tip
difference t1 (null -> True)  = t1
difference t1 t2   = hedgeDiff (const LT) (const GT) t1 t2

hedgeDiff :: (US a, Ord a) => (a -> Ordering) -> (a -> Ordering) -> USet a -> USet a -> USet a
hedgeDiff _ _ (null -> True) _ = tip
hedgeDiff cmplo cmphi (view -> Bin _ x l r) (null -> True) = join x (filterGt cmplo l) (filterLt cmphi r)
hedgeDiff cmplo cmphi t (view -> Bin _ x l r) = merge (hedgeDiff cmplo cmpx (trim cmplo cmpx t) l) (hedgeDiff cmpx cmphi (trim cmpx cmphi t) r)
  where
    cmpx = compare x

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}
-- | /O(n+m)/. The intersection of two sets.
-- Elements of the result come from the first set, so for example
--
-- > import qualified Data.Set as S
-- > data AB = A | B deriving Show
-- > instance Ord AB where compare _ _ = EQ
-- > instance Eq AB where _ == _ = True
-- > main = print (S.singleton A `S.intersection` S.singleton B,
-- >               S.singleton B `S.intersection` S.singleton A)
--
-- prints @(fromList [A],fromList [B])@.
intersection :: (US a, Ord a) => USet a -> USet a -> USet a
intersection (null -> True) _ = tip
intersection _ (null -> True) = tip
intersection t1@(view -> Bin s1 x1 l1 r1) t2@(view -> Bin s2 x2 l2 r2) =
   if s1 >= s2 then
      let (lt,found,gt) = splitLookup x2 t1
          tl            = intersection lt l2
          tr            = intersection gt r2
      in case found of
      Just x -> join x tl tr
      Nothing -> merge tl tr
   else let (lt,found,gt) = splitMember x1 t2
            tl            = intersection l1 lt
            tr            = intersection r1 gt
        in if found then join x1 tl tr
           else merge tl tr

{--------------------------------------------------------------------
  Filter and partition
--------------------------------------------------------------------}
-- | /O(n)/. Filter all elements that satisfy the predicate.
filter :: (US a, Ord a) => (a -> Bool) -> USet a -> USet a
filter p = go where
    go = viewk tip 
        (\_ x l r -> 
            if p x 
            then join x (go l) (go r) 
            else merge (go l) (go r)
        ) 

-- | /O(n)/. Partition the set into two sets, one with all elements that satisfy
-- the predicate and one with all elements that don't satisfy the predicate.
-- See also 'split'.
partition :: (US a, Ord a) => (a -> Bool) -> USet a -> (USet a,USet a)
partition p = go where
    go = viewk (tip,tip) 
        (\_ x l r -> 
            let 
                (l1,l2) = go l
                (r1,r2) = go r
            in if p x 
            then (join x l1 r1,merge l2 r2)
            else (merge l1 r1,join x l2 r2)
        )

{----------------------------------------------------------------------
  Map
----------------------------------------------------------------------}

-- | /O(n*log n)/. 
-- @'map' f s@ is the set obtained by applying @f@ to each element of @s@.
-- 
-- It's worth noting that the size of the result may be smaller if,
-- for some @(x,y)@, @x \/= y && f x == f y@

map :: (US a, US b, Ord a, Ord b) => (a->b) -> USet a -> USet b
map f = fromList . List.map f . toList

-- | /O(n)/. The 
--
-- @'mapMonotonic' f s == 'map' f s@, but works only when @f@ is monotonic.
-- /The precondition is not checked./
-- Semi-formally, we have:
-- 
-- > and [x < y ==> f x < f y | x <- ls, y <- ls] 
-- >                     ==> mapMonotonic f s == map f s
-- >     where ls = toList s

mapMonotonic :: (US a, US b) => (a->b) -> USet a -> USet b
mapMonotonic f (view -> Bin sz x l r) = bin sz (f x) (mapMonotonic f l) (mapMonotonic f r)
mapMonotonic _ _ = tip


{--------------------------------------------------------------------
  Fold
--------------------------------------------------------------------}
-- | /O(n)/. Fold over the elements of a set in an unspecified order.
fold :: US a => (a -> b -> b) -> b -> USet a -> b
fold f z s = foldr f z s

-- | /O(n)/. Post-order fold.
foldr :: US a => (a -> b -> b) -> b -> USet a -> b
--foldr f z (view -> Bin _ x l r) = foldr f (f x (foldr f z r)) l
--foldr _ z _ = z

foldr f z x | null x                     = z
            | (# x, l, r #) <- viewBin x = foldr f (f x (foldr f z r)) l 
{-# INLINE foldr #-}

{--------------------------------------------------------------------
  List variations 
--------------------------------------------------------------------}
-- | /O(n)/. The elements of a set.
elems :: US a => USet a -> [a]
elems x = toList x

{--------------------------------------------------------------------
  Lists 
--------------------------------------------------------------------}
-- | /O(n)/. Convert the set to a list of elements.
toList :: US a => USet a -> [a]
toList x = toAscList x
{-# INLINE toList #-}

-- | /O(n)/. Convert the set to an ascending list of elements.
toAscList :: US a => USet a -> [a]
toAscList = foldr (:) []


-- | /O(n*log n)/. Create a set from a list of elements.
fromList :: (US a, Ord a) => [a] -> USet a 
fromList = foldlStrict ins empty
  where
    ins t x = insert x t

{--------------------------------------------------------------------
  Building trees from ascending/descending lists can be done in linear time.
  
  Note that if [xs] is ascending that: 
    fromAscList xs == fromList xs
--------------------------------------------------------------------}
-- | /O(n)/. Build a set from an ascending list in linear time.
-- /The precondition (input list is ascending) is not checked./
fromAscList :: (US a, Eq a) => [a] -> USet a 
fromAscList xs
  = fromDistinctAscList (combineEq xs)
  where
  -- [combineEq xs] combines equal elements with [const] in an ordered list [xs]
  combineEq xs'
    = case xs' of
        []     -> []
        [x]    -> [x]
        (x:xx) -> combineEq' x xx

  combineEq' z [] = [z]
  combineEq' z (x:xs')
    | z==x      =   combineEq' z xs'
    | otherwise = z:combineEq' x xs'


-- | /O(n)/. Build a set from an ascending list of distinct elements in linear time.
-- /The precondition (input list is strictly ascending) is not checked./
fromDistinctAscList :: US a => [a] -> USet a 
fromDistinctAscList xs
  = build const (length xs) xs
  where
    -- 1) use continutations so that we use heap space instead of stack space.
    -- 2) special case for n==5 to build bushier trees. 
    build c 0 xs'  = c tip xs'
    build c 5 xs'  = case xs' of
                       (x1:x2:x3:x4:x5:xx) 
                            -> c (bin_ x4 (bin_ x2 (singleton x1) (singleton x3)) (singleton x5)) xx
                       _ -> error "fromDistinctAscList build 5"
    build c n xs'  = seq nr $ build (buildR nr c) nl xs'
                   where
                     nl = n `div` 2
                     nr = n - nl - 1

    buildR n c l (x:ys) = build (buildB l x c) n ys
    buildR _ _ _ []     = error "fromDistinctAscList buildR []"
    buildB l x c r zs   = c (bin_ x l r) zs

{--------------------------------------------------------------------
  Eq converts the set to a list. In a lazy setting, this 
  actually seems one of the faster methods to compare two trees 
  and it is certainly the simplest :-)
--------------------------------------------------------------------}
instance (US a, Eq a) => Eq (USet a) where
  t1 == t2  = (size t1 == size t2) && (toAscList t1 == toAscList t2)

{--------------------------------------------------------------------
  Ord 
--------------------------------------------------------------------}

instance (US a, Ord a) => Ord (USet a) where
    compare s1 s2 = compare (toAscList s1) (toAscList s2) 

{--------------------------------------------------------------------
  Show
--------------------------------------------------------------------}
instance (US a, Show a) => Show (USet a) where
  showsPrec p xs = showParen (p > 10) $
    showString "fromList " . shows (toList xs)

{--------------------------------------------------------------------
  Read
--------------------------------------------------------------------}
instance (US a, Read a, Ord a) => Read (USet a) where
#ifdef __GLASGOW_HASKELL__
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    fromList `fmap` readPrec

  readListPrec = readListPrecDefault
#else
  readsPrec p = readParen (p > 10) $ \ r -> do
    ("fromList",s) <- lex r
    (xs,t) <- reads s
    return (fromList xs,t)
#endif

{--------------------------------------------------------------------
  Utility functions that return sub-ranges of the original
  tree. Some functions take a comparison function as argument to
  allow comparisons against infinite values. A function [cmplo x]
  should be read as [compare lo x].

  [trim cmplo cmphi t]  A tree that is either empty or where [cmplo x == LT]
                        and [cmphi x == GT] for the value [x] of the root.
  [filterGt cmp t]      A tree where for all values [k]. [cmp k == LT]
  [filterLt cmp t]      A tree where for all values [k]. [cmp k == GT]

  [split k t]           Returns two trees [l] and [r] where all values
                        in [l] are <[k] and all keys in [r] are >[k].
  [splitMember k t]     Just like [split] but also returns whether [k]
                        was found in the tree.
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  [trim lo hi t] trims away all subtrees that surely contain no
  values between the range [lo] to [hi]. The returned tree is either
  empty or the key of the root is between @lo@ and @hi@.
--------------------------------------------------------------------}
trim :: US a => (a -> Ordering) -> (a -> Ordering) -> USet a -> USet a
trim cmplo cmphi t@(view -> Bin _ x l r)
  = case cmplo x of
      LT -> case cmphi x of
              GT -> t
              _  -> trim cmplo cmphi l
      _  -> trim cmplo cmphi r
trim _     _     _ = tip

{--------------------------------------------------------------------
  [filterGt x t] filter all values >[x] from tree [t]
  [filterLt x t] filter all values <[x] from tree [t]
--------------------------------------------------------------------}
filterGt :: US a => (a -> Ordering) -> USet a -> USet a
filterGt cmp (view -> Bin _ x l r)
  = case cmp x of
      LT -> join x (filterGt cmp l) r
      GT -> filterGt cmp r
      EQ -> r
filterGt _ _ = tip
      
filterLt :: US a => (a -> Ordering) -> USet a -> USet a
filterLt cmp (view -> Bin _ x l r)
  = case cmp x of
      LT -> filterLt cmp l
      GT -> join x l (filterLt cmp r)
      EQ -> l
filterLt _ _ = tip


{--------------------------------------------------------------------
  Split
--------------------------------------------------------------------}
-- | /O(log n)/. The expression (@'split' x set@) is a pair @(set1,set2)@
-- where @set1@ comprises the elements of @set@ less than @x@ and @set2@
-- comprises the elements of @set@ greater than @x@.
split :: (US a, Ord a) => a -> USet a -> (USet a,USet a)
split x (view -> Bin _ y l r)
  = case compare x y of
      LT -> let (lt,gt) = split x l in (lt,join y gt r)
      GT -> let (lt,gt) = split x r in (join y l lt,gt)
      EQ -> (l,r)
split _ _ = (tip,tip)

-- | /O(log n)/. Performs a 'split' but also returns whether the pivot
-- element was found in the original set.
splitMember :: (US a, Ord a) => a -> USet a -> (USet a,Bool,USet a)
splitMember x t = let (l,m,r) = splitLookup x t in
     (l,maybe False (const True) m,r)

-- | /O(log n)/. Performs a 'split' but also returns the pivot
-- element that was found in the original set.
splitLookup :: (US a, Ord a) => a -> USet a -> (USet a,Maybe a,USet a)
splitLookup x (view -> Bin _ y l r)
   = case compare x y of
       LT -> let (lt,found,gt) = splitLookup x l in (lt,found,join y gt r)
       GT -> let (lt,found,gt) = splitLookup x r in (join y l lt,found,gt)
       EQ -> (l,Just y,r)
splitLookup _ _ = (tip,Nothing,tip)

{--------------------------------------------------------------------
  Utility functions that maintain the balance properties of the tree.
  All constructors assume that all values in [l] < [x] and all values
  in [r] > [x], and that [l] and [r] are valid trees.
  
  In order of sophistication:
    [Bin sz x l r]    The type constructor.
    [bin_ x l r]      Maintains the correct size, assumes that both [l]
                      and [r] are balanced with respect to each other.
    [balance x l r]   Restores the balance and size.
                      Assumes that the original tree was balanced and
                      that [l] or [r] has changed by at most one element.
    [join x l r]      Restores balance and size. 

  Furthermore, we can construct a new tree from two trees. Both operations
  assume that all values in [l] < all values in [r] and that [l] and [r]
  are valid:
    [glue l r]        Glues [l] and [r] together. Assumes that [l] and
                      [r] are already balanced with respect to each other.
    [merge l r]       Merges two trees and restores balance.

  Note: in contrast to Adam's paper, we use (<=) comparisons instead
  of (<) comparisons in [join], [merge] and [balance]. 
  Quickcheck (on [difference]) showed that this was necessary in order 
  to maintain the invariants. It is quite unsatisfactory that I haven't 
  been able to find out why this is actually the case! Fortunately, it 
  doesn't hurt to be a bit more conservative.
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  Join 
--------------------------------------------------------------------}
join :: US a => a -> USet a -> USet a -> USet a
join x (null -> True) r  = insertMin x r
join x l (null -> True)  = insertMax x l
join x l@(view -> Bin sizeL y ly ry) r@(view -> Bin sizeR z lz rz)
  | delta*sizeL <= sizeR  = balance z (join x l lz) rz
  | delta*sizeR <= sizeL  = balance y ly (join x ry r)
  | otherwise             = bin_ x l r


-- insertMin and insertMax don't perform potentially expensive comparisons.
insertMax,insertMin :: US a => a -> USet a -> USet a 
insertMax x t
  = case view t of
      Bin _ y l r -> balance y l (insertMax x r)
      _ -> singleton x
             
insertMin x t
  = case view t of
      Bin _ y l r -> balance y (insertMin x l) r
      _ -> singleton x
             
{--------------------------------------------------------------------
  [merge l r]: merges two trees.
--------------------------------------------------------------------}
merge :: US a => USet a -> USet a -> USet a
merge (null -> True) r   = r
merge l (null -> True)   = l
merge l@(view -> Bin sizeL x lx rx) r@(view -> Bin sizeR y ly ry)
  | delta*sizeL <= sizeR = balance y (merge l ly) ry
  | delta*sizeR <= sizeL = balance x lx (merge rx r)
  | otherwise            = glue l r

{--------------------------------------------------------------------
  [glue l r]: glues two trees together.
  Assumes that [l] and [r] are already balanced with respect to each other.
--------------------------------------------------------------------}
glue :: US a => USet a -> USet a -> USet a
glue (null -> True) r = r
glue l (null -> True) = l
glue l r   
  | size l > size r = let (m,l') = deleteFindMax l in balance m l' r
  | otherwise       = let (m,r') = deleteFindMin r in balance m l r'


-- | /O(log n)/. Delete and find the minimal element.
-- 
-- > deleteFindMin set = (findMin set, deleteMin set)

deleteFindMin :: US a => USet a -> (a,USet a)
deleteFindMin t 
  = case view t of
      Bin _ x (null -> True) r -> (x,r)
      Bin _ x l r   -> let (xm,l') = deleteFindMin l in (xm,balance x l' r)
      Tip           -> (error "Set.deleteFindMin: can not return the minimal element of an empty set", tip)

-- | /O(log n)/. Delete and find the maximal element.
-- 
-- > deleteFindMax set = (findMax set, deleteMax set)
deleteFindMax :: US a => USet a -> (a,USet a)
deleteFindMax t
  = case view t of
      Bin _ x l (null -> True) -> (x,l)
      Bin _ x l r   -> let (xm,r') = deleteFindMax r in (xm,balance x l r')
      _ -> (error "Set.deleteFindMax: can not return the maximal element of an empty set", tip)

-- | /O(log n)/. Retrieves the minimal key of the set, and the set
-- stripped of that element, or 'Nothing' if passed an empty set.
minView :: US a => USet a -> Maybe (a, USet a)
minView (null -> True) = Nothing
minView x = Just (deleteFindMin x)

-- | /O(log n)/. Retrieves the maximal key of the set, and the set
-- stripped of that element, or 'Nothing' if passed an empty set.
maxView :: US a => USet a -> Maybe (a, USet a)
maxView (null -> True) = Nothing
maxView x = Just (deleteFindMax x)

{--------------------------------------------------------------------
  [balance x l r] balances two trees with value x.
  The sizes of the trees should balance after decreasing the
  size of one of them. (a rotation).

  [delta] is the maximal relative difference between the sizes of
          two trees, it corresponds with the [w] in Adams' paper,
          or equivalently, [1/delta] corresponds with the $\alpha$
          in Nievergelt's paper. Adams shows that [delta] should
          be larger than 3.745 in order to garantee that the
          rotations can always restore balance.         

  [ratio] is the ratio between an outer and inner sibling of the
          heavier subtree in an unbalanced setting. It determines
          whether a double or single rotation should be performed
          to restore balance. It is correspondes with the inverse
          of $\alpha$ in Adam's article.

  Note that:
  - [delta] should be larger than 4.646 with a [ratio] of 2.
  - [delta] should be larger than 3.745 with a [ratio] of 1.534.
  
  - A lower [delta] leads to a more 'perfectly' balanced tree.
  - A higher [delta] performs less rebalancing.

  - Balancing is automatic for random data and a balancing
    scheme is only necessary to avoid pathological worst cases.
    Almost any choice will do in practice
    
  - Allthough it seems that a rather large [delta] may perform better 
    than smaller one, measurements have shown that the smallest [delta]
    of 4 is actually the fastest on a wide range of operations. It
    especially improves performance on worst-case scenarios like
    a sequence of ordered insertions.

  Note: in contrast to Adams' paper, we use a ratio of (at least) 2
  to decide whether a single or double rotation is needed. Allthough
  he actually proves that this ratio is needed to maintain the
  invariants, his implementation uses a (invalid) ratio of 1. 
  He is aware of the problem though since he has put a comment in his 
  original source code that he doesn't care about generating a 
  slightly inbalanced tree since it doesn't seem to matter in practice. 
  However (since we use quickcheck :-) we will stick to strictly balanced 
  trees.
--------------------------------------------------------------------}
delta,ratio :: Int
delta = 4
ratio = 2

balance :: US a => a -> USet a -> USet a -> USet a
balance x l r
  | sizeL + sizeR <= 1    = bin sizeX x l r
  | sizeR >= delta*sizeL  = rotateL x l r
  | sizeL >= delta*sizeR  = rotateR x l r
  | otherwise             = bin sizeX x l r
  where
    sizeL = size l
    sizeR = size r
    sizeX = sizeL + sizeR + 1
{-# SPECIALIZE balance :: Int -> USet Int -> USet Int -> USet Int #-}

-- rotate
rotateL :: US a => a -> USet a -> USet a -> USet a
rotateL x l (viewBin -> (# v, ly, ry #))
  | size ly < ratio*size ry = singleL x l v ly ry
  | otherwise               = doubleL x l v ly ry

rotateR :: US a => a -> USet a -> USet a -> USet a
rotateR x (viewBin -> (# v, ly, ry #)) r
  | size ry < ratio*size ly = singleR x v ly ry r
  | otherwise               = doubleR x v ly ry r

singleL :: US a => a -> USet a -> a -> USet a -> USet a -> USet a
singleL x1 t1 x2 t2 t3 
    = bin_ x2 (bin_ x1 t1 t2) t3

singleR :: US a => a -> a -> USet a -> USet a -> USet a -> USet a
singleR x1 x2 t1 t2 t3 
    = bin_ x2 t1 (bin_ x1 t2 t3)

doubleL :: US a => a -> USet a -> a -> USet a -> USet a -> USet a
doubleL x1 t1 x2 (viewBin -> (# x3, t2, t3 #)) t4 
    = bin_ x3 (bin_ x1 t1 t2) (bin_ x2 t3 t4)

doubleR :: US a => a -> a -> USet a -> USet a -> USet a -> USet a
doubleR x1 x2 t1 (viewBin -> (# x3, t2, t3 #)) t4 
    = bin_ x3 (bin_ x2 t1 t2) (bin_ x1 t3 t4)

{--------------------------------------------------------------------
  The bin constructor maintains the size of the tree
--------------------------------------------------------------------}
bin_ :: US a => a -> USet a -> USet a -> USet a
bin_ x l r
  = bin (size l + size r + 1) x l r
{-# INLINE bin_ #-}


{--------------------------------------------------------------------
  Utilities
--------------------------------------------------------------------}
foldlStrict :: (a -> b -> a) -> a -> [b] -> a
foldlStrict f z xs
  = case xs of
      []     -> z
      (x:xx) -> let z' = f z x in seq z' (foldlStrict f z' xx)


{--------------------------------------------------------------------
  Debugging
--------------------------------------------------------------------}
-- | /O(n)/. Show the tree that implements the set. The tree is shown
-- in a compressed, hanging format.
showTree :: (US a, Show a) => USet a -> String
showTree s
  = showTreeWith True False s


{- | /O(n)/. The expression (@showTreeWith hang wide map@) shows
 the tree that implements the set. If @hang@ is
 @True@, a /hanging/ tree is shown otherwise a rotated tree is shown. If
 @wide@ is 'True', an extra wide version is shown.

> Set> putStrLn $ showTreeWith True False $ fromDistinctAscList [1..5]
> 4
> +--2
> |  +--1
> |  +--3
> +--5
> 
> Set> putStrLn $ showTreeWith True True $ fromDistinctAscList [1..5]
> 4
> |
> +--2
> |  |
> |  +--1
> |  |
> |  +--3
> |
> +--5
> 
> Set> putStrLn $ showTreeWith False True $ fromDistinctAscList [1..5]
> +--5
> |
> 4
> |
> |  +--3
> |  |
> +--2
>    |
>    +--1

-}
showTreeWith :: (US a, Show a) => Bool -> Bool -> USet a -> String
showTreeWith hang wide t
  | hang      = (showsTreeHang wide [] t) ""
  | otherwise = (showsTree wide [] [] t) ""

showsTree :: (US a, Show a) => Bool -> [String] -> [String] -> USet a -> ShowS
showsTree wide lbars rbars t
  = case view t of
      Tip -> showsBars lbars . showString "|\n"
      Bin _ x (null -> True) (null -> True)
          -> showsBars lbars . shows x . showString "\n" 
      Bin _ x l r
          -> showsTree wide (withBar rbars) (withEmpty rbars) r .
             showWide wide rbars .
             showsBars lbars . shows x . showString "\n" .
             showWide wide lbars .
             showsTree wide (withEmpty lbars) (withBar lbars) l

showsTreeHang :: (US a, Show a) => Bool -> [String] -> USet a -> ShowS
showsTreeHang wide bars t
  = case view t of
      Tip -> showsBars bars . showString "|\n" 
      Bin _ x (null -> True) (null -> True) 
          -> showsBars bars . shows x . showString "\n" 
      Bin _ x l r
          -> showsBars bars . shows x . showString "\n" . 
             showWide wide bars .
             showsTreeHang wide (withBar bars) l .
             showWide wide bars .
             showsTreeHang wide (withEmpty bars) r

showWide :: Bool -> [String] -> String -> String
showWide wide bars 
  | wide      = showString (concat (reverse bars)) . showString "|\n" 
  | otherwise = id

showsBars :: [String] -> ShowS
showsBars bars
  = case bars of
      [] -> id
      _  -> showString (concat (reverse (tail bars))) . showString node

node :: String
node           = "+--"

withBar, withEmpty :: [String] -> [String]
withBar bars   = "|  ":bars
withEmpty bars = "   ":bars

{--------------------------------------------------------------------
  Assertions
--------------------------------------------------------------------}
-- | /O(n)/. Test if the internal set structure is valid.
valid :: (US a, Ord a) => USet a -> Bool
valid t
  = balanced t && ordered t && validsize t

ordered :: (US a, Ord a) => USet a -> Bool
ordered t
  = bounded (const True) (const True) t
  where
    bounded lo hi t'
      = case view t' of
          Bin _ x l r -> (lo x) && (hi x) && bounded lo (<x) l && bounded (>x) hi r
          _ -> True

balanced :: US a => USet a -> Bool
balanced t
  = case view t of
      Bin _ _ l r -> (size l + size r <= 1 || (size l <= delta*size r && size r <= delta*size l)) &&
                     balanced l && balanced r
      _ -> True

validsize :: US a => USet a -> Bool
validsize t
  = (realsize t == Just (size t))
  where
    realsize t'
      = case view t' of
          Bin sz _ l r -> case (realsize l,realsize r) of
                            (Just n,Just m)  | n+m+1 == sz  -> Just sz
                            _                -> Nothing
          _ -> Just 0

{-
{--------------------------------------------------------------------
  Testing
--------------------------------------------------------------------}
testTree :: [Int] -> USet Int
testTree xs   = fromList xs
test1 = testTree [1..20]
test2 = testTree [30,29..10]
test3 = testTree [1,4,6,89,2323,53,43,234,5,79,12,9,24,9,8,423,8,42,4,8,9,3]

{--------------------------------------------------------------------
  QuickCheck
--------------------------------------------------------------------}

{-
qcheck prop
  = check config prop
  where
    config = Config
      { configMaxTest = 500
      , configMaxFail = 5000
      , configSize    = \n -> (div n 2 + 3)
      , configEvery   = \n args -> let s = show n in s ++ [ '\b' | _ <- s ]
      }
-}


{--------------------------------------------------------------------
  Arbitrary, reasonably balanced trees
--------------------------------------------------------------------}
instance (US a, Enum a) => Arbitrary (USet a) where
  arbitrary = sized (arbtree 0 maxkey)
            where maxkey  = 10000

arbtree :: (US a, Enum a) => Int -> Int -> Int -> Gen (USet a)
arbtree lo hi n
  | n <= 0        = return tip
  | lo >= hi      = return tip
  | otherwise     = do{ i  <- choose (lo,hi)
                      ; m  <- choose (1,30)
                      ; let (ml,mr)  | m==(1::Int)= (1,2)
                                     | m==2       = (2,1)
                                     | m==3       = (1,1)
                                     | otherwise  = (2,2)
                      ; l  <- arbtree lo (i-1) (n `div` ml)
                      ; r  <- arbtree (i+1) hi (n `div` mr)
                      ; return (bin_ (toEnum i) l r)
                      }  


{--------------------------------------------------------------------
  Valid tree's
--------------------------------------------------------------------}
forValid :: (US a, Enum a,Show a,Testable b) => (USet a -> b) -> Property
forValid f
  = forAll arbitrary $ \t -> 
--    classify (balanced t) "balanced" $
    classify (size t == 0) "empty" $
    classify (size t > 0  && size t <= 10) "small" $
    classify (size t > 10 && size t <= 64) "medium" $
    classify (size t > 64) "large" $
    balanced t ==> f t

forValidIntTree :: Testable a => (USet Int -> a) -> Property
forValidIntTree f
  = forValid f

forValidUnitTree :: Testable a => (USet Int -> a) -> Property
forValidUnitTree f
  = forValid f


prop_Valid 
  = forValidUnitTree $ \t -> valid t

{--------------------------------------------------------------------
  Single, Insert, Delete
--------------------------------------------------------------------}
prop_Single :: Int -> Bool
prop_Single x
  = (insert x empty == singleton x)

prop_InsertValid :: Int -> Property
prop_InsertValid k
  = forValidUnitTree $ \t -> valid (insert k t)

prop_InsertDelete :: Int -> USet Int -> Property
prop_InsertDelete k t
  = not (member k t) ==> delete k (insert k t) == t

prop_DeleteValid :: Int -> Property
prop_DeleteValid k
  = forValidUnitTree $ \t -> 
    valid (delete k (insert k t))

{--------------------------------------------------------------------
  Balance
--------------------------------------------------------------------}
prop_Join :: Int -> Property 
prop_Join x
  = forValidUnitTree $ \t ->
    let (l,r) = split x t
    in valid (join x l r)

prop_Merge :: Int -> Property 
prop_Merge x
  = forValidUnitTree $ \t ->
    let (l,r) = split x t
    in valid (merge l r)


{--------------------------------------------------------------------
  Union
--------------------------------------------------------------------}
prop_UnionValid :: Property
prop_UnionValid
  = forValidUnitTree $ \t1 ->
    forValidUnitTree $ \t2 ->
    valid (union t1 t2)

prop_UnionInsert :: Int -> USet Int -> Bool
prop_UnionInsert x t
  = union t (singleton x) == insert x t

prop_UnionAssoc :: USet Int -> USet Int -> USet Int -> Bool
prop_UnionAssoc t1 t2 t3
  = union t1 (union t2 t3) == union (union t1 t2) t3

prop_UnionComm :: USet Int -> USet Int -> Bool
prop_UnionComm t1 t2
  = (union t1 t2 == union t2 t1)


prop_DiffValid
  = forValidUnitTree $ \t1 ->
    forValidUnitTree $ \t2 ->
    valid (difference t1 t2)

prop_Diff :: [Int] -> [Int] -> Bool
prop_Diff xs ys
  =  toAscList (difference (fromList xs) (fromList ys))
    == List.sort ((List.\\) (nub xs)  (nub ys))

prop_IntValid
  = forValidUnitTree $ \t1 ->
    forValidUnitTree $ \t2 ->
    valid (intersection t1 t2)

prop_Int :: [Int] -> [Int] -> Bool
prop_Int xs ys
  =  toAscList (intersection (fromList xs) (fromList ys))
    == List.sort (nub ((List.intersect) (xs)  (ys)))

{--------------------------------------------------------------------
  Lists
--------------------------------------------------------------------}
prop_Ordered
  = forAll (choose (5,100)) $ \n ->
    let xs = [0..n::Int]
    in fromAscList xs == fromList xs

prop_List :: [Int] -> Bool
prop_List xs
  = (sort (nub xs) == toList (fromList xs))
-}


newtype Boxed a = Boxed a deriving (Eq,Ord,Show,Read,Bounded)
instance US (Boxed a) where
    data USet (Boxed a) = BoxedTip | BoxedBin {-# UNPACK #-} !Size (Boxed a) !(USet (Boxed a)) !(USet (Boxed a))
    view BoxedTip = Tip
    view (BoxedBin s i l r) = Bin s i l r
    viewk t _ BoxedTip = t 
    viewk _ k (BoxedBin s i l r) = k s i l r
    viewBin (BoxedBin _ i l r) = (# i, l, r #)
    tip = BoxedTip
    bin = BoxedBin
    size BoxedTip =0
    size (BoxedBin s _ _ _) = s
    null BoxedTip = True
    null _ = False

instance US Char where
    data USet Char = CharTip | CharBin {-# UNPACK #-} !Size {-# UNPACK #-} !Char !(USet Char) !(USet Char)
    view CharTip = Tip
    view (CharBin s i l r) = Bin s i l r
    viewk t _ CharTip = t 
    viewk _ k (CharBin s i l r) = k s i l r
    viewBin (CharBin _ i l r) = (# i, l, r #)
    tip = CharTip
    bin = CharBin
    null CharTip = True
    null _ = False

instance US Int where
    data USet Int = IntTip | IntBin {-# UNPACK #-} !Size {-# UNPACK #-} !Int !(USet Int) !(USet Int)
    view IntTip = Tip
    view (IntBin s i l r) = Bin s i l r
    viewk t _ IntTip = t 
    viewk _ k (IntBin s i l r) = k s i l r
    viewBin (IntBin _ i l r) = (# i, l, r #)
    size IntTip = 0
    size (IntBin s _ _ _) = s
    tip = IntTip
    bin = IntBin
    null IntTip = True
    null _ = False

instance US Integer where
    data USet Integer = IntegerTip | IntegerBin {-# UNPACK #-} !Size {-# UNPACK #-} !Integer !(USet Integer) !(USet Integer)
    view IntegerTip = Tip
    view (IntegerBin s i l r) = Bin s i l r
    viewk t _ IntegerTip = t 
    viewk _ k (IntegerBin s i l r) = k s i l r
    viewBin (IntegerBin _ i l r) = (# i, l, r #)
    tip = IntegerTip
    bin = IntegerBin
    null IntegerTip = True
    null _ = False

instance US Int8 where
    data USet Int8 = Int8Tip | Int8Bin {-# UNPACK #-} !Size {-# UNPACK #-} !Int8 !(USet Int8) !(USet Int8)
    view Int8Tip = Tip
    view (Int8Bin s i l r) = Bin s i l r
    viewk t _ Int8Tip = t 
    viewk _ k (Int8Bin s i l r) = k s i l r
    viewBin (Int8Bin _ i l r) = (# i, l, r #)
    tip = Int8Tip
    bin = Int8Bin
    null Int8Tip = True
    null _ = False

instance US Int16 where
    data USet Int16 = Int16Tip | Int16Bin {-# UNPACK #-} !Size {-# UNPACK #-} !Int16 !(USet Int16) !(USet Int16)
    view Int16Tip = Tip
    view (Int16Bin s i l r) = Bin s i l r
    viewk t _ Int16Tip = t 
    viewk _ k (Int16Bin s i l r) = k s i l r
    viewBin (Int16Bin _ i l r) = (# i, l, r #)
    tip = Int16Tip
    bin = Int16Bin
    null Int16Tip = True
    null _ = False

instance US Int32 where
    data USet Int32 = Int32Tip | Int32Bin {-# UNPACK #-} !Size {-# UNPACK #-} !Int32 !(USet Int32) !(USet Int32)
    view Int32Tip = Tip
    view (Int32Bin s i l r) = Bin s i l r
    viewk t _ Int32Tip = t 
    viewk _ k (Int32Bin s i l r) = k s i l r
    viewBin (Int32Bin _ i l r) = (# i, l, r #)
    tip = Int32Tip
    bin = Int32Bin
    null Int32Tip = True
    null _ = False

instance US Int64 where
    data USet Int64 = Int64Tip | Int64Bin {-# UNPACK #-} !Size {-# UNPACK #-} !Int64 !(USet Int64) !(USet Int64)
    view Int64Tip = Tip
    view (Int64Bin s i l r) = Bin s i l r
    viewk t _ Int64Tip = t 
    viewk _ k (Int64Bin s i l r) = k s i l r
    viewBin (Int64Bin _ i l r) = (# i, l, r #)
    tip = Int64Tip
    bin = Int64Bin
    null Int64Tip = True
    null _ = False

instance US Word8 where
    data USet Word8 = Word8Tip | Word8Bin {-# UNPACK #-} !Size {-# UNPACK #-} !Word8 !(USet Word8) !(USet Word8)
    view Word8Tip = Tip
    view (Word8Bin s i l r) = Bin s i l r
    viewk t _ Word8Tip = t 
    viewk _ k (Word8Bin s i l r) = k s i l r
    viewBin (Word8Bin _ i l r) = (# i, l, r #)
    tip = Word8Tip
    bin = Word8Bin
    null Word8Tip = True
    null _ = False

instance US Word16 where
    data USet Word16 = Word16Tip | Word16Bin {-# UNPACK #-} !Size {-# UNPACK #-} !Word16 !(USet Word16) !(USet Word16)
    view Word16Tip = Tip
    view (Word16Bin s i l r) = Bin s i l r
    viewk t _ Word16Tip = t 
    viewk _ k (Word16Bin s i l r) = k s i l r
    viewBin (Word16Bin _ i l r) = (# i, l, r #)
    bin = Word16Bin
    tip = Word16Tip
    null Word16Tip = True
    null _ = False

instance US Word32 where
    data USet Word32 = Word32Tip | Word32Bin {-# UNPACK #-} !Size {-# UNPACK #-} !Word32 !(USet Word32) !(USet Word32)
    view Word32Tip = Tip
    view (Word32Bin s i l r) = Bin s i l r
    viewk t _ Word32Tip = t 
    viewk _ k (Word32Bin s i l r) = k s i l r
    viewBin (Word32Bin _ i l r) = (# i, l, r #)
    tip = Word32Tip
    bin = Word32Bin
    null Word32Tip = True
    null _ = False

instance US Word64 where
    data USet Word64 = Word64Tip | Word64Bin {-# UNPACK #-} !Size {-# UNPACK #-} !Word64 !(USet Word64) !(USet Word64)
    view Word64Tip = Tip
    view (Word64Bin s i l r) = Bin s i l r
    viewk t _ Word64Tip = t 
    viewk _ k (Word64Bin s i l r) = k s i l r
    viewBin (Word64Bin _ i l r) = (# i, l, r #)
    tip = Word64Tip
    bin = Word64Bin
    null Word64Tip = True
    null _ = False

instance US Double where
    data USet Double = DoubleTip | DoubleBin {-# UNPACK #-} !Size {-# UNPACK #-} !Double !(USet Double) !(USet Double)
    view DoubleTip = Tip
    view (DoubleBin s i l r) = Bin s i l r
    viewk t _ DoubleTip = t 
    viewk _ k (DoubleBin s i l r) = k s i l r
    viewBin (DoubleBin _ i l r) = (# i, l, r #)
    tip = DoubleTip
    bin = DoubleBin
    null DoubleTip = True
    null _ = False

instance US Float where
    data USet Float = FloatTip | FloatBin {-# UNPACK #-} !Size {-# UNPACK #-} !Float !(USet Float) !(USet Float)
    view FloatTip = Tip
    view (FloatBin s i l r) = Bin s i l r
    viewk t _ FloatTip = t 
    viewk _ k (FloatBin s i l r) = k s i l r
    viewBin (FloatBin _ i l r) = (# i, l, r #)
    tip = FloatTip
    bin = FloatBin
    null FloatTip = True
    null _ = False

