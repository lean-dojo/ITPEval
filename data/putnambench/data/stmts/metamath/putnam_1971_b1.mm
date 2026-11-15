$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1971_b1: an idempotent binary operation satisfying the cyclic
  law (x * y) * z = (y * z) * x is associative and commutative.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary carrier is the set S, and F is an arbitrary total binary
  operation represented as a function from S X. S to S. Application to an
  ordered pair represents the source operation. The antecedent is exactly
  the idempotence and cyclic laws, and the conclusion retains the separate
  universal associativity and commutativity assertions.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F S x y z $.

  putnambench-putnam-1971-b1 $a |- A. S
    A. F e. ( S ^m ( S X. S ) )
      (
        (
          A. x e. S
            ( F ` <. x , x >. ) = x
          /\
          A. x e. S A. y e. S A. z e. S
            ( F ` <. ( F ` <. x , y >. ) , z >. )
            =
            ( F ` <. ( F ` <. y , z >. ) , x >. )
        )
        ->
        (
          A. x e. S A. y e. S A. z e. S
            ( F ` <. ( F ` <. x , y >. ) , z >. )
            =
            ( F ` <. x , ( F ` <. y , z >. ) >. )
          /\
          A. x e. S A. y e. S
            ( F ` <. x , y >. ) = ( F ` <. y , x >. )
        )
      )
  $.
$}
