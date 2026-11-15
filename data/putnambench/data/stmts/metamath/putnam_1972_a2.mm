$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1972_a2: binary operations satisfying x * (x * y) = y and
  (y * x) * x = y are commutative, but need not be associative.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary carrier is the set S, and F is an arbitrary total binary
  operation represented as a function from S X. S to S. Application to an
  ordered pair represents the source operation. The first conjunct quantifies
  over every such carrier and operation; the second keeps the carrier and
  nonassociative operation internally existential, as in the source statement.

  The final declaration is the single unproved $a corpus statement; this
  statement file contributes no $p proof statement.
$)

${
  $d F S x y z $.

  putnambench-putnam-1972-a2 $a |- (
    (
      A. S
        A. F e. ( S ^m ( S X. S ) )
          (
            A. x e. S A. y e. S
              (
                ( F ` <. x , ( F ` <. x , y >. ) >. ) = y
                /\
                ( F ` <. ( F ` <. y , x >. ) , x >. ) = y
              )
            ->
            A. x e. S A. y e. S
              ( F ` <. x , y >. ) = ( F ` <. y , x >. )
          )
    )
    /\
    E. S
      E. F e. ( S ^m ( S X. S ) )
        (
          A. x e. S A. y e. S
            (
              ( F ` <. x , ( F ` <. x , y >. ) >. ) = y
              /\
              ( F ` <. ( F ` <. y , x >. ) , x >. ) = y
            )
          /\
          -. A. x e. S A. y e. S A. z e. S
            ( F ` <. x , ( F ` <. y , z >. ) >. )
            =
            ( F ` <. ( F ` <. x , y >. ) , z >. )
        )
  ) $.
$}
