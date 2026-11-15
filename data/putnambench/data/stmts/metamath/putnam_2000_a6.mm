$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2000_a6: an integer polynomial iterated from zero can return to zero
  at a positive index only if its first or second iterate is zero. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( Poly1 ` ZZring ) is set.mm's ring of finite-support univariate
  polynomials over the integers, and eval1 evaluates such a polynomial at an
  integer. The function a ranges over all integer-valued sequences indexed by
  NN0. The recurrence and initial value are exactly the source hypotheses,
  while NN is the class of positive integers used for the internal return
  index.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a f m n $.

  putnambench-putnam-2000-a6 $a |-
    A. f e. ( Base ` ( Poly1 ` ZZring ) )
      A. a e. ( ZZ ^m NN0 )
        (
          (
            ( a ` 0 ) = 0
            /\
            A. n e. NN0
              ( a ` ( n + 1 ) )
              =
              ( ( ( eval1 ` ZZring ) ` f ) ` ( a ` n ) )
          )
          ->
          (
            E. m e. NN
              ( a ` m ) = 0
            ->
            (
              ( a ` 1 ) = 0
              \/
              ( a ` 2 ) = 0
            )
          )
        )
  $.
$}
