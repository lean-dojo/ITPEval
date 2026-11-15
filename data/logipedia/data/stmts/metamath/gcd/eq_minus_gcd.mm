$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.eq_minus_gcd (logipedia__metamath__gcd.eq_minus_gcd), catalog title
  "gcd.eq_minus_gcd": for every pair of natural numbers, natural
  coefficients make one of the two truncated differences of multiples equal
  their greatest common divisor. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM multiplication and gcd are the
  corresponding natural-number operations. Each conditional
    if ( y <_ x , x - y , 0 )
  is exactly the source truncated subtraction nat.minus x y. The restricted
  universal and existential quantifiers, disjunction, and equality preserve
  the source statement. The final declaration is the single unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d a b m n $.

  logipedia-gcd-eq-minus-gcd $a |-
    A. m e. NN0 A. n e. NN0
      E. a e. NN0 E. b e. NN0
        (
          if (
            ( b x. m ) <_ ( a x. n ) ,
            ( ( a x. n ) - ( b x. m ) ) ,
            0
          ) = ( n gcd m )
          \/
          if (
            ( a x. n ) <_ ( b x. m ) ,
            ( ( b x. m ) - ( a x. n ) ) ,
            0
          ) = ( n gcd m )
        )
  $.
$}
