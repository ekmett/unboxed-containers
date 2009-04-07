#!/usr/bin/perl


sub poly ($$) { 
    my ($type,$var) = @_;
    return ("Boxed $var","(Boxed $var)","(Boxed $var)") if $type eq "Boxed";
    return ($type,$type,"{-# UNPACK #-} !$type");
}

our @types = qw(Int Char Int8 Int16 Int32 Int64 Word8 Word16 Word32 Word64 Double Float Integer Boxed);

foreach my $type (@types) {
    my ($poly,$qpoly,$member) = poly $type, "a";
    my $tag = "$type";

    print qq(

instance US $qpoly where
    data USet $qpoly = ${tag}Tip | ${tag}Bin {-# UNPACK #-} !Size ${member} !(USet $qpoly) !(USet $qpoly)
    view ${tag}Tip = Tip
    view (${tag}Bin s i l r) = Bin s i l r
    tip = ${tag}Tip
    bin = ${tag}Bin);

    foreach my $type2 (@types) {

=for pairs
        my ($poly2,$qpoly2,$member2) = poly $type2, "b";
        my $tuple = "($poly,$poly2)";
        my $tag = "$type$type2";
        print qq(
    
instance US $tuple where
    data USet $tuple = ${tag}Tip | ${tag}Bin {-# UNPACK #-} !Size ${member} ${member2} !(USet $tuple) !(USet $tuple)
    view ${tag}Tip = Tip
    view (${tag}Bin s i j l r) = Bin s (i,j) l r
    tip = ${tag}Tip
    bin s (i,j) = ${tag}Bin s i j);

=cut

=for triples
        foreach my $type3 (@types) {
            my ($poly3,$qpoly3,$member3) = poly $type3, "c";
            my $tuple = "($poly,$poly2,$poly3)";
            my $tag = "$type$type2$type3";
            print qq(
    
instance US $tuple where
    data USet $tuple = ${tag}Tip | ${tag}Bin {-# UNPACK #-} !Size ${member} ${member2} ${member3} !(USet $tuple) !(USet $tuple)
    view ${tag}Tip = Tip
    view (${tag}Bin s i j k l r) = Bin s (i,j,k) l r
    tip = ${tag}Tip
    bin s (i,j,k) = ${tag}Bin s i j k);

        }
=cut

    }
}

print "\n\n";

