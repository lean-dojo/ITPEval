$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_b6: one quarter is the largest real exponent for which a
  positive natural-valued function can satisfy the specified iterated
  growth inequality on every positive integer. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The function g ranges over all total functions from NN0 to NN0, matching
  Lean's natural-number domain including zero. The restricted quantifiers
  over NN are exactly the source hypotheses 0 < n; they require g(n) to be
  positive there but impose no extra condition on g(0).

  Under that positivity condition, g(g(n)) is positive for every positive
  n, so set.mm's complex-power operation ^c agrees with Lean's real-power
  operation on the displayed base and real exponent. The first conjunct
  supplies an admissible function at exponent 1 / 4. The second says every
  real exponent admitting such a function is at most 1 / 4. Together these
  are definitionally the source IsGreatest statement with its annotated
  solution value. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d g n r $.

  putnambench-putnam-2025-b6 $a |-
    (
      E. g e. ( NN0 ^m NN0 )
        (
          A. n e. NN
            0 < ( g ` n )
          /\
          A. n e. NN
            (
              (
                ( g ` ( g ` n ) )
                ^c
                ( 1 / 4 )
              )
              <_
              (
                ( g ` ( n + 1 ) )
                -
                ( g ` n )
              )
            )
        )
      /\
      A. r e. RR
        (
          (
            E. g e. ( NN0 ^m NN0 )
              (
                A. n e. NN
                  0 < ( g ` n )
                /\
                A. n e. NN
                  (
                    (
                      ( g ` ( g ` n ) )
                      ^c
                      r
                    )
                    <_
                    (
                      ( g ` ( n + 1 ) )
                      -
                      ( g ` n )
                    )
                  )
              )
          )
          ->
          r <_ ( 1 / 4 )
        )
    )
  $.
$}
