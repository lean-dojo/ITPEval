$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1984_b3: every finite set with at least two elements admits a
  right-cancellative binary operation that is nonassociative at every
  ordered triple. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary finite carrier is the set S. The witness F is a total
  function from S X. S to S, so application to an ordered pair represents
  the source binary operation. Its existential quantifier remains inside
  the universal quantifier over finite carriers.

  For every x, y, and z in S, the first conjunct is exactly right
  cancellation, and the second asserts the source's pointwise failure of
  associativity. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d F S x y z $.

  putnambench-putnam-1984-b3 $a |- A. S e. Fin
    (
      2 <_ ( # ` S )
      ->
      E. F e. ( S ^m ( S X. S ) )
        A. x e. S A. y e. S A. z e. S
          (
            (
              ( F ` <. x , z >. ) = ( F ` <. y , z >. )
              ->
              x = y
            )
            /\
            ( F ` <. x , ( F ` <. y , z >. ) >. )
            =/=
            ( F ` <. ( F ` <. x , y >. ) , z >. )
          )
    )
  $.
$}
