$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1994_a1: every positive real sequence satisfying the binary-tree
  inequality has partial sums tending to positive infinity. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over all real-valued sequences indexed by the nonnegative
  integers. Quantification over NN in the hypothesis is exactly
  quantification over natural indices n >= 1.

  The conclusion expands convergence of the partial sums to positive
  infinity: for every real bound b, all sums from k = 1 through N exceed
  that bound once N is past a natural threshold. This is the restricted-
  quantifier form of the atTop-to-atTop limit in the Lean and Isabelle
  sources. Positivity makes it consistent with the Rocq formulation as
  nonexistence of a finite limit.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A N b k m n $.

  putnambench-putnam-1994-a1 $a |- A. A e. ( RR ^m NN0 )
    (
      A. n e. NN
        (
          0 < ( A ` n )
          /\
          ( A ` n )
          <_
          (
            ( A ` ( 2 x. n ) )
            +
            ( A ` ( ( 2 x. n ) + 1 ) )
          )
        )
      ->
      A. b e. RR
        E. m e. NN0
          A. N e. NN0
            (
              m <_ N
              ->
              b
              <_
              (
                sum_ k e. ( 1 ... N )
                  ( A ` k )
              )
            )
    )
  $.
$}
