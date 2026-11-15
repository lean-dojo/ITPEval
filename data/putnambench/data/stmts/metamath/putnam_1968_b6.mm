$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1968_b6: no sequence of compact sets of rational numbers contains
  every compact set of rational numbers as a subset of one of its terms.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  K ranges over all functions from NN0 to the full power set of QQ. For a
  subset of QQ, restriction of the standard real topology gives the usual
  rational subspace topology, so membership of that restricted topology in
  Comp is exactly compactness of the rational set.

  The second universal quantifier ranges over every subset S of QQ and keeps
  the containing index existentially quantified. Thus the assertion is the
  negation of the same cofinal-sequence property stated in the Lean and
  Isabelle sources. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d K n S $.

  putnambench-putnam-1968-b6 $a |- -. E. K
    (
      K : NN0 --> ~P QQ
      /\
      (
        A. n e. NN0
          (
            ( ( TopOpen ` RRfld ) |`t ( K ` n ) )
            e. Comp
          )
        /\
        A. S e. ~P QQ
          (
            ( ( ( TopOpen ` RRfld ) |`t S ) e. Comp )
            ->
            E. n e. NN0 S C_ ( K ` n )
          )
      )
    )
  $.
$}
