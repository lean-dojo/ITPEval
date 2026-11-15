$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_a4: the expected dyadically weighted sum of independent
  uniform random variables through the first ascent is
  2 * exp(1/2) - 3. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P22A4Uniform P Y states that the real random variable Y has the uniform
  probability law on the closed unit interval: every Borel set a has
  probability equal to the Lebesgue measure of a intersected with [0,1].

  P22A4Independent P X expands mutual independence into the finite-family
  product identity for arbitrary Borel preimages. P22A4Stop X w is the union,
  hence the powerset supremum, of all initial segments 0...m for which
  X_l(w) > X_(l+1)(w) at every l < m. This is exactly the supplied Lean
  definition of k(w); for continuous independent uniform variables it agrees
  almost surely with stopping at the first strict ascent.

  P22A4Series X K w is set.mm's unbounded sum over the indices in K when that
  sum converges to a real number, and is zero otherwise. This totalization
  matches Lean's tsum over the subtype determined by k(w), including its value
  on nonsummable families. Since every summand is nonnegative and the complete
  dyadic series is at most one, P22A4Expectation P S uses the layer-cake
  identity E[S] = integral from 0 to 1 of P(S > t). The conclusion inlines the
  explicit solution value recorded in the Lean source. Every declaration below
  is an unproved $a statement; this database contains no $p proof declaration.
$)

$c P22A4Uniform P22A4Independent P22A4Stop P22A4Series
   P22A4Expectation $.

p22a4-uniform-syntax $a wff ( P22A4Uniform P Y ) $.
p22a4-independent-syntax $a wff ( P22A4Independent P X ) $.
p22a4-stop-syntax $a class ( P22A4Stop X w ) $.
p22a4-series-syntax $a class ( P22A4Series X K w ) $.
p22a4-expectation-syntax $a class ( P22A4Expectation P S ) $.

${
  $d P Y a $.

  p22a4-uniform-definition $a |- (
    ( P22A4Uniform P Y )
    <->
    A. a e. BrSiga
      ( P ` ( `' Y " a ) )
      =
      ( vol ` ( a i^i ( 0 [,] 1 ) ) )
  ) $.
$}

${
  $d P X f i s $.

  p22a4-independent-definition $a |- (
    ( P22A4Independent P X )
    <->
    A. s e. ( Fin i^i ~P NN0 )
      A. f e. ( BrSiga ^m s )
        (
          P
          `
          (
            U. dom P
            i^i
            |^|_ i e. s
              ( `' ( X ` i ) " ( f ` i ) )
          )
        )
        =
        prod_ i e. s
          ( P ` ( `' ( X ` i ) " ( f ` i ) ) )
  ) $.
$}

${
  $d X l m w $.

  p22a4-stop-definition $a |- (
    P22A4Stop X w
  ) = (
    U_ m e.
      {
        m e. NN0 |
          A. l e. NN0
            (
              l < m
              ->
              ( ( X ` ( l + 1 ) ) ` w )
              <
              ( ( X ` l ) ` w )
            )
      }
      ( 0 ... m )
  ) $.
$}

${
  $d X K i w $.

  p22a4-series-definition $a |- (
    P22A4Series X K w
  ) = (
    if (
      (
        sum_ i e. K
          (
            ( ( X ` i ) ` w )
            /
            ( 2 ^ ( i + 1 ) )
          )
      )
      e.
      RR ,
      sum_ i e. K
        (
          ( ( X ` i ) ` w )
          /
          ( 2 ^ ( i + 1 ) )
        ) ,
      0
    )
  ) $.
$}

${
  $d P S t w $.

  p22a4-expectation-definition $a |- (
    P22A4Expectation P S
  ) = (
    S. ( 0 [,] 1 )
      (
        P
        `
        {
          w e. U. dom P |
            t < ( S ` w )
        }
      )
      _d t
  ) $.
$}

${
  $d i k p s w x $.

  putnambench-putnam-2022-a4 $a |-
    A. p e. Prob
    A. x e. ( ( rRndVar ` p ) ^m NN0 )
    A. k e. ( ( ~P NN0 ) ^m U. dom p )
    A. s e. ( RR ^m U. dom p )
      (
        (
          (
            A. i e. NN0
              ( P22A4Uniform p ( x ` i ) )
            /\
            ( P22A4Independent p x )
          )
          /\
          (
            A. w e. U. dom p
              ( k ` w ) = ( P22A4Stop x w )
            /\
            A. w e. U. dom p
              ( s ` w ) = ( P22A4Series x ( k ` w ) w )
          )
        )
        ->
        ( P22A4Expectation p s )
        =
        (
          (
            2
            x.
            ( exp ` ( 1 / 2 ) )
          )
          -
          3
        )
      )
  $.
$}
