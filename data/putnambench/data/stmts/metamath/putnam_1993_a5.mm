$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1993_a5: rationality of the sum of three specified real interval
  integrals of a squared rational function. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Set.mm's S. binder is the real Lebesgue integral. The three open intervals
  exactly match the Lean source; changing endpoint inclusion does not affect
  these integrals and therefore also matches the Isabelle and Rocq interval
  integrals. The integrand inlines

    ((x^2 - x) / (x^3 - 3x + 1))^2.

  Membership of the resulting real sum in QQ is exactly its rationality.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

putnambench-putnam-1993-a5 $a |- (
  (
    (
      S. ( ( -u ; 1 0 0 ) (,) ( -u ; 1 0 ) )
        (
          (
            ( ( x ^ 2 ) - x )
            /
            (
              ( ( x ^ 3 ) - ( 3 x. x ) )
              +
              1
            )
          )
          ^ 2
        )
        _d x
      +
      S. ( ( 1 / ; 1 0 1 ) (,) ( 1 / ; 1 1 ) )
        (
          (
            ( ( x ^ 2 ) - x )
            /
            (
              ( ( x ^ 3 ) - ( 3 x. x ) )
              +
              1
            )
          )
          ^ 2
        )
        _d x
    )
    +
    S. ( ( ; 1 0 1 / ; 1 0 0 ) (,) ( ; 1 1 / ; 1 0 ) )
      (
        (
          ( ( x ^ 2 ) - x )
          /
          (
            ( ( x ^ 3 ) - ( 3 x. x ) )
            +
            1
          )
        )
        ^ 2
      )
      _d x
  )
  e. QQ
) $.
