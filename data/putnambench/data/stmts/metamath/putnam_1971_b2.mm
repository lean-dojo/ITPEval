$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1971_b2: classification of the real functions satisfying
  F(x) + F((x-1)/x) = 1+x away from 0 and 1.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P71B2F is the total real function recorded by the ground truths as the
  unique solution on RR \ { 0, 1 }. The final assertion separately states
  that P71B2F satisfies the functional equation and that every total real
  function satisfying it agrees with P71B2F on that domain. This is the
  source conjunction after expanding its property and singleton solution-set
  definitions.

  The function definition and final corpus statement are unproved $a
  declarations; this database contains no $p proof statement.
$)

$c P71B2F $.

p71b2-function-syntax $a class P71B2F $.

p71b2-function-definition $a |- P71B2F =
  (
    x e. RR |->
      (
        ( ( ( x ^ 3 ) - ( x ^ 2 ) ) - 1 )
        /
        ( ( 2 x. x ) x. ( x - 1 ) )
      )
  )
$.

${
  $d f x $.

  putnambench-putnam-1971-b2 $a |- (
    (
      A. x e. { x e. RR | ( x =/= 0 /\ x =/= 1 ) }
        (
          ( P71B2F ` x )
          +
          ( P71B2F ` ( ( x - 1 ) / x ) )
        )
        =
        ( 1 + x )
    )
    /\
    A. f e. ( RR ^m RR )
      (
        (
          A. x e. { x e. RR | ( x =/= 0 /\ x =/= 1 ) }
            (
              ( f ` x )
              +
              ( f ` ( ( x - 1 ) / x ) )
            )
            =
            ( 1 + x )
        )
        ->
        A. x e. { x e. RR | ( x =/= 0 /\ x =/= 1 ) }
          ( f ` x ) = ( P71B2F ` x )
      )
  ) $.
$}
