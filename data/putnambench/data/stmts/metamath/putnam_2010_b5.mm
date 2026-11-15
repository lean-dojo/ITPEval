$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_b5: nonexistence of a strictly increasing differentiable real
  function satisfying f'(x) = f(f(x)) for every real x. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  f ranges over all total real-valued functions on the reals. The first
  restricted universal is exactly strict increase, while containment of RR
  in dom ( RR _D f ) expresses differentiability at every real point. The
  final restricted universal is the differential equation pointwise on RR.

  The ground-truth solution is False, so negating the internally quantified
  existence statement is logically equivalent to its biconditional with
  False. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d f x y $.

  putnambench-putnam-2010-b5 $a |- -.
    E. f e. ( RR ^m RR )
      (
        A. x e. RR A. y e. RR
          (
            x < y
            ->
            ( f ` x ) < ( f ` y )
          )
        /\
        (
          RR C_ dom ( RR _D f )
          /\
          A. x e. RR
            ( ( RR _D f ) ` x )
            =
            ( f ` ( f ` x ) )
        )
      )
  $.
$}
