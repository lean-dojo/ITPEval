$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_a1: classification of the real lines that intersect
  y = log(1 + x^2) in exactly one real point. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The equality of sets in the Lean and Isabelle statements is rendered
  pointwise by universally quantifying the real slope a and intercept b.
  The restricted unique existential says exactly that the intersection
  equation has one real solution.

  The right side inlines the explicit solution annotation from the primary
  Lean source. For 0 < abs(a) < 1, the two displayed real numbers are the
  critical points of x |-> log(1 + x^2) - a*x; the strict inequalities put
  b below its local minimum or above its local maximum. Set.mm's log is the
  natural logarithm, as required by the published problem and primary
  statement. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d a b x $.

  putnambench-putnam-2022-a1 $a |- A. a e. RR A. b e. RR
    (
      E! x e. RR
        (
          ( ( a x. x ) + b )
          =
          ( log ` ( 1 + ( x ^ 2 ) ) )
        )
      <->
      (
        (
          a = 0
          /\
          b = 0
        )
        \/
        (
          1 <_ ( abs ` a )
          \/
          (
            (
              0 < ( abs ` a )
              /\
              ( abs ` a ) < 1
            )
            /\
            (
              b
              <
              (
                (
                  log
                  `
                  (
                    1
                    +
                    (
                      (
                        (
                          1
                          -
                          ( sqrt ` ( 1 - ( a ^ 2 ) ) )
                        )
                        /
                        a
                      )
                      ^
                      2
                    )
                  )
                )
                -
                (
                  a
                  x.
                  (
                    (
                      1
                      -
                      ( sqrt ` ( 1 - ( a ^ 2 ) ) )
                    )
                    /
                    a
                  )
                )
              )
              \/
              (
                (
                  log
                  `
                  (
                    1
                    +
                    (
                      (
                        (
                          1
                          +
                          ( sqrt ` ( 1 - ( a ^ 2 ) ) )
                        )
                        /
                        a
                      )
                      ^
                      2
                    )
                  )
                )
                -
                (
                  a
                  x.
                  (
                    (
                      1
                      +
                      ( sqrt ` ( 1 - ( a ^ 2 ) ) )
                    )
                    /
                    a
                  )
                )
              )
              <
              b
            )
          )
        )
      )
    )
  $.
$}
