$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1975_a2: the real coefficient pairs for which every complex root
  of a monic quadratic lies strictly inside the unit disk. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The coefficients b and c range over all real numbers, while z ranges over
  all complex numbers. Set.mm's complex arithmetic embeds the real
  coefficients canonically, and abs is the complex modulus. The right side
  is the explicit solution predicate recorded in the ground-truth sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d b c z $.

  putnambench-putnam-1975-a2 $a |-
    A. b e. RR A. c e. RR
      (
        A. z e. CC
          (
            (
              (
                ( z ^ 2 )
                +
                ( b x. z )
              )
              +
              c
            )
            =
            0
            ->
            ( abs ` z ) < 1
          )
        <->
        (
          c < 1
          /\
          (
            ( -u 1 ) < ( c - b )
            /\
            ( -u 1 ) < ( c + b )
          )
        )
      )
  $.
$}
