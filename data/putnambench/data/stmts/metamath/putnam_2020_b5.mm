$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2020_b5: four complex numbers of modulus one, none equal to one,
  make the stated sum of three, their negatives, and their product nonzero.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's CC is the complex plane and abs is complex modulus. The four
  complex numbers remain independently universally quantified, and the
  antecedent states each unit-modulus and non-one hypothesis explicitly.
  The arithmetic expression uses the source's left-associated subtraction
  and multiplication.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d a b c d $.

  putnambench-putnam-2020-b5 $a |-
    A. a e. CC A. b e. CC A. c e. CC A. d e. CC
      (
        (
          (
            (
              ( abs ` a ) = 1
              /\
              ( abs ` b ) = 1
            )
            /\
            (
              ( abs ` c ) = 1
              /\
              ( abs ` d ) = 1
            )
          )
          /\
          (
            (
              a =/= 1
              /\
              b =/= 1
            )
            /\
            (
              c =/= 1
              /\
              d =/= 1
            )
          )
        )
        ->
        (
          (
            ( ( ( 3 - a ) - b ) - c )
            -
            d
          )
          +
          ( ( ( a x. b ) x. c ) x. d )
        )
        =/=
        0
      )
  $.
$}
