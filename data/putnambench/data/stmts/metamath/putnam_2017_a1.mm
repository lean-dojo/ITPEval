$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2017_a1: classification of the positive integers omitted by the
  smallest positive-integer set containing 2 and closed under the stated
  square-root and shifted-square rules. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the set of integers. The antecedent expands the source
  predicate IsQualifying: S consists of positive integers, contains 2,
  contains a positive integer whenever it contains its square, and contains
  (n + 5)^2 whenever it contains n. Its second conjunct says that S is
  contained in every other qualifying integer set, which is exactly the
  source IsLeast condition after definitional substitution.

  The conclusion identifies the positive integers outside S with exactly 1
  and the positive multiples of 5. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d S T n $.

  putnambench-putnam-2017-a1 $a |- A. S
    (
      (
        (
          (
            S C_ ZZ
            /\
            A. n e. S 0 < n
          )
          /\
          (
            2 e. S
            /\
            (
              A. n e. ZZ
                (
                  (
                    0 < n
                    /\
                    ( n ^ 2 ) e. S
                  )
                  ->
                  n e. S
                )
              /\
              A. n e. S ( ( n + 5 ) ^ 2 ) e. S
            )
          )
        )
        /\
        A. T
          (
            (
              (
                T C_ ZZ
                /\
                A. n e. T 0 < n
              )
              /\
              (
                2 e. T
                /\
                (
                  A. n e. ZZ
                    (
                      (
                        0 < n
                        /\
                        ( n ^ 2 ) e. T
                      )
                      ->
                      n e. T
                    )
                  /\
                  A. n e. T ( ( n + 5 ) ^ 2 ) e. T
                )
              )
            )
            ->
            S C_ T
          )
      )
      ->
      {
        n e. ZZ |
        (
          0 < n
          /\
          -. n e. S
        )
      }
      =
      {
        n e. ZZ |
        (
          0 < n
          /\
          (
            n = 1
            \/
            5 || n
          )
        )
      }
    )
  $.
$}
