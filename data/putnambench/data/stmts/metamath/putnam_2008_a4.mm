$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2008_a4: the reciprocal series for the recursively defined real
  function f(x) = x when x <= exp(1) and f(x) = x f(log x) otherwise does
  not converge. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is set.mm's class of total real-valued functions. The hypothesis
  preserves the recursive equation pointwise on all real inputs, including
  the source conditional at exp(1).

  For each n in NN0, the finite sum over 0 ..^ n has terms
  1 / f(k + 1), so it is exactly the first-n partial sum used by the Lean
  source. The negated existential expands failure of convergence to any real
  limit in the epsilon-threshold form. This is logically equivalent to the
  source biconditional between convergence and False. The final declaration
  is the single unproved $a corpus statement; this database has no $p proof
  statement.
$)

${
  $d e f k m n r x $.

  putnambench-putnam-2008-a4 $a |- A. f e. ( RR ^m RR )
    (
      (
        A. x e. RR
          ( f ` x )
          =
          if (
            x <_ ( exp ` 1 ) ,
            x ,
            x x. ( f ` ( log ` x ) )
          )
      )
      ->
      -.
      E. r e. RR
        A. e e. RR
          (
            0 < e
            ->
            E. m e. NN0
              A. n e. NN0
                (
                  m <_ n
                  ->
                  (
                    abs
                    `
                    (
                      (
                        sum_ k e. ( 0 ..^ n )
                          ( 1 / ( f ` ( k + 1 ) ) )
                      )
                      -
                      r
                    )
                  )
                  <
                  e
                )
          )
    )
  $.
$}
