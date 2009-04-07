#!/usr/bin/perl

use strict qw(vars);

sub poly ($$) { 
    my ($type,$var) = @_;
    return ("Boxed $var","(Boxed $var)","(Boxed $var)",$var) if $type eq "Boxed";
    return ("Complex $1","(Complex $1)","{-# UNPACK #-} !(Complex $1)",$var) if $type =~ m/Complex(.*)/;
    return ($type,$type,"{-# UNPACK #-} !$type",$var);
}

sub instance {
    my ($types) = @_;
    my $var = 97;
    my @typeinfo = map { [poly $_, chr($var++)] } @$types;
    my $tag = join '', @$types;
    my $tuple = scalar @$types == 1 ? $typeinfo[0][1] : '(' .  join(',', map { $_->[0] } @typeinfo) . ')';
    my $members = join '', map { $_->[2] } @typeinfo;
    my $vartuple = '(' . join(',', map { $_->[3] } @typeinfo) . ')';
    my $varlist = join(' ', map { $_->[3] } @typeinfo);
    print qq(

instance US $tuple where
    data USet $tuple = ${tag}Tip | ${tag}Bin {-# UNPACK #-} !Size ${members} !(USet $tuple) !(USet $tuple)
    view ${tag}Tip = Tip
    view (${tag}Bin s $varlist l r) = Bin s $vartuple l r
    tip = ${tag}Tip
    bin s $vartuple = ${tag}Bin s $varlist);
}

our @types = qw(Int Char Int8 Int16 Int32 Int64 Word8 Word16 Word32 Word64 Double Float Integer Boxed);
our @common = qw(Int Char Int32 Int64 Integer Boxed Double Word32 Word64);

foreach my $type (@types) { 
    instance [$type];
}

# n^2 seems to be too slow, so omit the stuff that could just be contained in larger types
#foreach my $type1 (@common) {
#    foreach my $type2 (@common) { 
#        instance [$type1,$type2];
#    }
#}

# n^9 is way to slow. just include repetitions.
foreach my $type (@types) { 
    instance [$type,$type];
    instance [$type,$type,$type];
    instance [$type,$type,$type,$type];
    instance [$type,$type,$type,$type,$type];
    instance [$type,$type,$type,$type,$type,$type];
    instance [$type,$type,$type,$type,$type,$type,$type];
    instance [$type,$type,$type,$type,$type,$type,$type,$type];
    instance [$type,$type,$type,$type,$type,$type,$type,$type,$type];
}

print "\n\n";
