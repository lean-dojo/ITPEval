$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1973_b2: a unit complex number with rational real and imaginary
  parts has rational modulus of z^(2n) - 1 for every integer n.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Membership of Re(z) and Im(z) in QQ is equivalent to the source
  existential rational-coordinate equalities under the standard embeddings.
  Likewise, membership of the resulting real modulus in QQ is equivalent to
  the internally existential rational witness in the conclusion.

  SetMM exponentiation accepts a complex base and an integer exponent, so
  2n ranges over exactly the source even integer exponents. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d n z $.

  putnambench-putnam-1973-b2 $a |- A. z e. CC
    (
      (
        (
          ( Re ` z ) e. QQ
          /\
          ( Im ` z ) e. QQ
        )
        /\
        ( abs ` z ) = 1
      )
      ->
      A. n e. ZZ
        ( abs ` ( ( z ^ ( 2 x. n ) ) - 1 ) ) e. QQ
    )
  $.
$}
