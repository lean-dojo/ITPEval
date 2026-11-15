$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1980_b6: the canonical reduced denominator of a recursively defined
  rational quantity G(d,p) is not divisible by the prime p when
  1 < d <= p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  G ranges over all rational-valued functions on pairs of integers, matching
  the Lean and Rocq sources. Every pair used by the recurrence or conclusion
  has nonnegative coordinates; restriction to NN0 X. NN0 and arbitrary
  extension outside it therefore give the natural-pair presentation in the
  Isabelle source and this integer-pair presentation in both directions.

  The restricted quantifiers over NN0 preserve the natural-number indices.
  The interval d ... n and sum_ binder give the inclusive finite sum from d
  through n. SetMM's denom is the positive denominator of the unique reduced
  fraction representation of a rational number. Thus nondivisibility by p is
  exactly the source conclusion. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d G d i n p $.

  putnambench-putnam-1980-b6 $a |-
    A. G e. ( QQ ^m ( ZZ X. ZZ ) )
      (
        A. d e. NN0 A. n e. NN0
          (
            d <_ n
            ->
            (
              (
                d = 1
                ->
                ( G ` <. d , n >. ) = ( 1 / n )
              )
              /\
              (
                1 < d
                ->
                ( G ` <. d , n >. )
                =
                (
                  ( d / n )
                  x.
                  sum_ i e. ( d ... n )
                    ( G ` <. ( d - 1 ) , ( i - 1 ) >. )
                )
              )
            )
          )
        ->
        A. d e. NN0 A. p e. NN0
          (
            (
              (
                1 < d
                /\
                d <_ p
              )
              /\
              p e. Prime
            )
            ->
            -. p || ( denom ` ( G ` <. d , p >. ) )
          )
      )
  $.
$}
