$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2012_a2: a commutative associative binary operation whose left
  translations are surjective satisfies right cancellation. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary carrier is the set S, and F is an arbitrary total binary
  operation represented as a function from S X. S to S. Application to an
  ordered pair represents the source operation.

  The antecedent states commutativity, associativity, and, for every x and y
  in S, the existence of z in S with F(x,z) = y. The witness z remains inside
  those universal quantifiers. The conclusion retains arbitrary a, b, and c
  in S and the implication from F(a,c) = F(b,c) to a = b.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F S a b c x y z $.

  putnambench-putnam-2012-a2 $a |- A. S
    A. F e. ( S ^m ( S X. S ) )
      (
        (
          (
            A. x e. S A. y e. S
              ( F ` <. x , y >. ) = ( F ` <. y , x >. )
            /\
            A. x e. S A. y e. S A. z e. S
              ( F ` <. ( F ` <. x , y >. ) , z >. )
              =
              ( F ` <. x , ( F ` <. y , z >. ) >. )
          )
          /\
          A. x e. S A. y e. S
            E. z e. S
              ( F ` <. x , z >. ) = y
        )
        ->
        A. a e. S A. b e. S A. c e. S
          (
            ( F ` <. a , c >. ) = ( F ` <. b , c >. )
            ->
            a = b
          )
      )
  $.
$}
