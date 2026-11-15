$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1980_b1: characterization of the real constants c for which
  (exp(x) + exp(-x)) / 2 is at most exp(c x^2) for every real x.
  Such constants are exactly those with c at least 1 / 2. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The restricted universal quantifiers preserve the source domains c, x in
  RR. The source solution set is inlined on the right side as the defining
  inequality 1 / 2 <= c. The left side uses set.mm's real exponential,
  arithmetic, order, and natural-number exponentiation operations directly.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d c x $.

  putnambench-putnam-1980-b1 $a |- A. c e. RR
    (
      A. x e. RR
        (
          (
            (
              ( exp ` x )
              +
              ( exp ` ( -u x ) )
            )
            /
            2
          )
          <_
          ( exp ` ( c x. ( x ^ 2 ) ) )
        )
      <->
      ( 1 / 2 ) <_ c
    )
  $.
$}
