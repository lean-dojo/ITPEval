$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2016_b2: characterization of the power-law asymptotic for the
  counting function of squarish positive integers. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P16B2Square says that an integer is the square of a nonnegative integer.
  P16B2Squarish says that an integer is either square or has square distance
  from a nearest integer square; the universal quantifier over NN0 retains
  the source's nearest-square condition.

  For positive N, the class 1 ... N is the inclusive integer interval and
  the cardinality in the final assertion is exactly S(N). Since N is
  positive, N ^c a agrees with the source real power N^a. The standard
  sequence relation ~~> expresses the limit as N tends to infinity.

  The explicit solution (3/4, 4/3) is from the published problem and the
  Rocq source. Inlining the source predicates S and p makes the first
  disjunct their stated characterization of every positive limit pair. The
  second disjunct retains the source alternative that no positive pair has
  the required limit. All declarations are unproved $a statement or
  definition encodings; this database contains no $p proof declaration.
$)

$c P16B2Square P16B2Squarish $.

p16b2-square-syntax $a wff ( P16B2Square A ) $.
p16b2-squarish-syntax $a wff ( P16B2Squarish A ) $.

${
  $d A k $.

  p16b2-square-definition $a |- (
    ( P16B2Square A )
    <->
    E. k e. NN0 A = ( k ^ 2 )
  ) $.
$}

${
  $d A v w $.

  p16b2-squarish-definition $a |- (
    ( P16B2Squarish A )
    <->
    (
      A e. ZZ
      /\
      (
        ( P16B2Square A )
        \/
        E. w e. ZZ
          (
            (
              P16B2Square
              ( abs ` ( A - ( w ^ 2 ) ) )
            )
            /\
            A. v e. NN0
              (
                ( abs ` ( A - ( w ^ 2 ) ) )
                <_
                ( abs ` ( A - ( v ^ 2 ) ) )
              )
          )
      )
    )
  ) $.
$}

${
  $d N a b i $.

  putnambench-putnam-2016-b2 $a |-
    (
      (
        A. a e. RR A. b e. RR
          (
            (
              a = ( 3 / 4 )
              /\
              b = ( 4 / 3 )
            )
            <->
            (
              (
                0 < a
                /\
                0 < b
              )
              /\
              (
                (
                  N e. NN |->
                    (
                      (
                        #
                        `
                        {
                          i e. ( 1 ... N ) |
                          ( P16B2Squarish i )
                        }
                      )
                      /
                      ( N ^c a )
                    )
                )
                ~~>
                b
              )
            )
          )
      )
      \/
      -. E. a e. RR E. b e. RR
        (
          (
            0 < a
            /\
            0 < b
          )
          /\
          (
            (
              N e. NN |->
                (
                  (
                    #
                    `
                    {
                      i e. ( 1 ... N ) |
                      ( P16B2Squarish i )
                    }
                  )
                  /
                  ( N ^c a )
                )
            )
            ~~>
            b
          )
        )
    )
  $.
$}
