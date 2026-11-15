$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_a3: the real series of positive-branch arccotangents at
  n^2 + n + 1 sums to pi / 2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over all total real-valued functions. Its antecedent is exactly
  the source characterization of arccot on nonnegative reals: A(t) lies in
  (0, pi/2] and cot(A(t)) = t. SetMM's cot is the standard cotangent,
  definitionally equal to cos(x) / sin(x) on this interval, so the separate
  cot function and its defining equality in the Lean and Rocq sources have
  been eliminated without changing the proposition.

  The sum over NN0 is SetMM's convergent infinite real-series sum. Its nth
  term is A(n^2 + n + 1), with the natural index canonically regarded as a
  real argument. The right side is the explicit Rocq solution and the value
  annotated in the Lean and Isabelle sources. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  declaration.
$)

${
  $d A n t $.

  putnambench-putnam-1986-a3 $a |- A. A e. ( RR ^m RR )
    (
      A. t e. RR
        (
          0 <_ t
          ->
          (
            0 < ( A ` t )
            /\
            (
              ( A ` t ) <_ ( _pi / 2 )
              /\
              ( cot ` ( A ` t ) ) = t
            )
          )
        )
      ->
      (
        sum_ n e. NN0
          ( A ` ( ( ( n ^ 2 ) + n ) + 1 ) )
      )
      =
      ( _pi / 2 )
    )
  $.
$}
