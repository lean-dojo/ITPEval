$(
  Statement-only formalization of Thousand Theorems corpus artifact Q318767
  (thousand-theorems__metamath__Q318767), "Abel's theorem": convergence of
  the coefficient partial sums implies that the associated complex power
  series tends to the same limit as its argument approaches one within every
  positive-width Stolz cone; for real coefficients, the power series tends
  to that limit as its argument approaches one from the left. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Q318767Partial is the sum of F(i) over i in {0, ..., M - 1}, matching the
  finite range sum in the Lean hypotheses. Q318767Power is the infinite sum
  of F(n) Z^n. Q318767CoeffLimit gives the epsilon form of convergence of the
  partial sums at infinity.

  Q318767ComplexLimit is the epsilon-delta form of convergence relative to
  the Stolz cone |Im(z)| < S (1 - Re(z)). Q318767RealLimit is the analogous
  relative limit on the real half-line x < 1. Thus the two final assertions
  render respectively the complex theorem and its real left-limit
  specialization from the Lean source. They are unproved $a assertions and
  this file has no $p statement.

  SetMM's unbounded sum denotes the series limit when it converges and the
  empty set otherwise, while Lean's tsum is totalized. Under
  Q318767CoeffLimit the coefficients are bounded, so Q318767Power converges
  whenever |Z| < 1. A sufficiently small neighborhood of 1 inside either a
  positive-width Stolz cone or the real set x < 1 lies in that unit disk, so
  the nonconvergent branch is never observed by the limit assertions.
$)

$c
  Q318767Partial
  Q318767Power
  Q318767CoeffLimit
  Q318767ComplexLimit
  Q318767RealLimit
$.

q318767-partial-syntax $a class ( Q318767Partial F M ) $.
q318767-power-syntax $a class ( Q318767Power F Z ) $.
q318767-coeff-limit-syntax $a wff ( Q318767CoeffLimit F L ) $.
q318767-complex-limit-syntax $a wff ( Q318767ComplexLimit F L S ) $.
q318767-real-limit-syntax $a wff ( Q318767RealLimit F L ) $.

${
  $d F M n $.

  q318767-partial-definition $a |- ( Q318767Partial F M ) =
    sum_ n e. ( 0 ..^ M ) ( F ` n )
  $.
$}

${
  $d F Z n $.

  q318767-power-definition $a |- ( Q318767Power F Z ) =
    sum_ n e. NN0 ( ( F ` n ) x. ( Z ^ n ) )
  $.
$}

${
  $d F L M N e $.

  q318767-coeff-limit-definition $a |- (
    ( Q318767CoeffLimit F L )
    <->
    A. e e. RR+
      E. N e. NN0
        A. M e. ( ZZ>= ` N )
          ( abs ` ( ( Q318767Partial F M ) - L ) ) < e
  ) $.
$}

${
  $d F L S d e z $.

  q318767-complex-limit-definition $a |- (
    ( Q318767ComplexLimit F L S )
    <->
    A. e e. RR+
      E. d e. RR+
        A. z e. CC
          (
            (
              ( abs ` ( Im ` z ) ) < ( S x. ( 1 - ( Re ` z ) ) )
              /\
              ( abs ` ( z - 1 ) ) < d
            )
            ->
            ( abs ` ( ( Q318767Power F z ) - L ) ) < e
          )
  ) $.
$}

${
  $d F L d e x $.

  q318767-real-limit-definition $a |- (
    ( Q318767RealLimit F L )
    <->
    A. e e. RR+
      E. d e. RR+
        A. x e. RR
          (
            (
              x < 1
              /\
              ( abs ` ( x - 1 ) ) < d
            )
            ->
            ( abs ` ( ( Q318767Power F x ) - L ) ) < e
          )
  ) $.
$}

${
  $d F L S $.

  thousand-theorems-q318767-complex-abel $a |-
    A. F e. ( CC ^m NN0 )
      A. L e. CC
        A. S e. RR
          (
            (
              ( Q318767CoeffLimit F L )
              /\
              0 < S
            )
            ->
            ( Q318767ComplexLimit F L S )
          )
  $.
$}

${
  $d F L $.

  thousand-theorems-q318767-real-abel $a |-
    A. F e. ( RR ^m NN0 )
      A. L e. RR
        (
          ( Q318767CoeffLimit F L )
          ->
          ( Q318767RealLimit F L )
        )
  $.
$}
