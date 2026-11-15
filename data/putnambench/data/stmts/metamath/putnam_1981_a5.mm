$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1981_a5: for every real polynomial P, the polynomial
  Q(x) = (x^2 + 1) P(x) P'(x) + x (P(x)^2 + P'(x)^2) has at
  least 2n - 1 distinct real zeros, where n counts the distinct
  real zeros of P greater than 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P81A5NCard implements the finite-cardinality convention used by
  Lean's Set.ncard and Isabelle's card: it is zero for an infinite
  set. P81A5Der is formal differentiation in the univariate
  polynomial ring over the real field, and P81A5Q is the polynomial
  construction in the problem. The final assertion states the claim
  directly because the source's annotated solution proposition is True.
  All declarations below are unproved $a statements; there is no $p
  proof declaration in this file.
$)

$c P81A5NCard P81A5Der P81A5Q $.

p81a5-ncard-syntax $a class P81A5NCard $.
p81a5-der-syntax $a class P81A5Der $.
p81a5-q-syntax $a class P81A5Q $.

p81a5-ncard-definition $a |- P81A5NCard =
  ( s e. _V |-> if ( s e. Fin , ( # ` s ) , 0 ) ) $.

p81a5-der-definition $a |- P81A5Der =
  ( p e. ( Base ` ( Poly1 ` RRfld ) ) |->
    ( ( ( 1o mPSDer RRfld ) ` (/) ) ` p ) ) $.

p81a5-q-definition $a |- P81A5Q =
  ( p e. ( Base ` ( Poly1 ` RRfld ) ) |->
    ( ( ( ( ( 2 ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) ) )
                  ( var1 ` RRfld ) )
              ( +g ` ( Poly1 ` RRfld ) )
              ( 1r ` ( Poly1 ` RRfld ) ) )
            ( .r ` ( Poly1 ` RRfld ) ) p )
          ( .r ` ( Poly1 ` RRfld ) ) ( P81A5Der ` p ) )
      ( +g ` ( Poly1 ` RRfld ) )
      ( ( var1 ` RRfld )
        ( .r ` ( Poly1 ` RRfld ) )
        ( ( 2 ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) ) ) p )
          ( +g ` ( Poly1 ` RRfld ) )
          ( 2 ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) ) )
              ( P81A5Der ` p ) ) ) ) ) ) $.

${
  $d P x $.
  putnambench-putnam-1981-a5 $a |- A. P e. ( Base ` ( Poly1 ` RRfld ) )
    ( ( ( 2 x. ( P81A5NCard `
              { x e. RR | ( 1 < x /\
                ( ( ( ( eval1 ` RRfld ) ` P ) ` x ) = 0 ) ) } ) )
          - 1 )
      <_ ( P81A5NCard `
            { x e. RR |
              ( ( ( ( eval1 ` RRfld ) ` ( P81A5Q ` P ) ) ` x )
                = 0 ) } ) ) $.
$}
