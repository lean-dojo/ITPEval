$(
  Statement-only formalization of "Descartes Rule of Signs" from the Hundred
  Theorems corpus artifact 100: coefficient sign variations bound the positive
  roots of a polynomial counted with multiplicity, and over the reals the
  difference is even. This file contains no proof.
$)

$[ library/set.mm $]

$(
  Poly1 ` R is set.mm's finite-support univariate polynomial ring over R, coe1
  is its coefficient function, and eval1 supplies its ordinary evaluation.

  ( R HT100Var F ) is the finite set of pairs of consecutive nonzero
  coefficient indices whose coefficients have opposite signs. Consecutive
  means that every coefficient at an intermediate index is zero.

  ( R HT100PosMult F ) represents positive roots with multiplicity. It is
  explicitly empty when F is the zero polynomial. Otherwise its pair
  <. x , k >. is present exactly when x is positive, k is a positive integer,
  and (X - x)^k divides F in Poly1 ` R. Thus its finite cardinality is the sum
  of the multiplicities of all positive roots.

  The first conjunct is the ordered-commutative-ring inequality stated by the
  Lean source, including the zero polynomial, for which both counting classes
  are empty. The second is the sharper real-polynomial equality from the HOL
  Light and Isabelle sources, under its nonzero hypothesis: sign variations
  equal positive-root multiplicity plus an even nonnegative integer. All
  declarations below are unproved $a assertions; this file contains no $p
  proof.
$)

$c HT100Var HT100PosMult $.

ht100-var-syntax $a class ( R HT100Var F ) $.
ht100-pos-mult-syntax $a class ( R HT100PosMult F ) $.

${
  $d F R i j k $.

  ht100-var-definition $a |- ( R HT100Var F ) = {
    <. i , j >. |
    (
      (
        i e. NN0
        /\
        (
          j e. NN0
          /\
          i < j
        )
      )
      /\
      (
        (
          (
            ( ( coe1 ` F ) ` i )
            ( .r ` R )
            ( ( coe1 ` F ) ` j )
          )
          ( lt ` R )
          ( 0g ` R )
        )
        /\
        A. k e. NN0
          (
            ( i < k /\ k < j )
            ->
            ( ( coe1 ` F ) ` k ) = ( 0g ` R )
          )
      )
    )
  } $.
$}

${
  $d F R k x $.

  ht100-pos-mult-definition $a |- ( R HT100PosMult F ) = {
    <. x , k >. |
    (
      F =/= ( 0g ` ( Poly1 ` R ) )
      /\
      (
        (
          x e. ( Base ` R )
          /\
          ( 0g ` R ) ( lt ` R ) x
        )
        /\
        (
          k e. NN
          /\
          (
            (
              k
              ( .g ` ( mulGrp ` ( Poly1 ` R ) ) )
              (
                ( var1 ` R )
                ( -g ` ( Poly1 ` R ) )
                ( ( algSc ` ( Poly1 ` R ) ) ` x )
              )
            )
            ( ||r ` ( Poly1 ` R ) )
            F
          )
        )
      )
    )
  } $.
$}

${
  $d d f r $.

  hundred-theorems-100-descartes-rule-of-signs $a |- (
    (
      A. r e. ( oRing i^i CRing )
      A. f e. ( Base ` ( Poly1 ` r ) )
        ( # ` ( r HT100PosMult f ) )
        <_
        ( # ` ( r HT100Var f ) )
    )
    /\
    (
      A. f e. ( Base ` ( Poly1 ` RRfld ) )
        (
          f =/= ( 0g ` ( Poly1 ` RRfld ) )
          ->
          E. d e. NN0
            (
              d e. Even
              /\
              ( # ` ( RRfld HT100Var f ) ) =
                (
                  ( # ` ( RRfld HT100PosMult f ) )
                  +
                  d
                )
            )
        )
    )
  ) $.
$}
