-- Statement-only formalization of corpus artifact hundred-theorems__agda__076,
-- "Fourier Series": every square-integrable real function on [-pi, pi] is the
-- L2-limit of its normalized trigonometric Fourier partial sums. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      Either (lessOrEqual x y) (lessOrEqual y x)
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      Both (lessOrEqual zeroR oneR) (zeroR != oneR)

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqual x upper) ->
              lessOrEqual supremum upper))

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqual reals x y) (x != y)

maximum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left _ = y
... | right _ = x

power :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
power reals x zero =
  oneR reals
power reals x (suc n) =
  multiply reals (power reals x n) x

factorial : Nat -> Nat
factorial zero = suc zero
factorial (suc n) = suc n * factorial n

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

sumThrough :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumThrough reals term zero =
  term zero
sumThrough reals term (suc n) =
  add reals
    (sumThrough reals term n)
    (term (suc n))

ConvergesTo :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      Both
        (StrictLess reals
          (subtract reals limit epsilon)
          (sequence n))
        (StrictLess reals
          (sequence n)
          (add reals limit epsilon)))

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals term limit =
  ConvergesTo reals
    (\ n -> sumFirst reals n term)
    limit

alternatingPower :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
alternatingPower reals n =
  power reals (negate reals (oneR reals)) n

sineTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
sineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingPower reals n)
      (power reals x (suc ((suc (suc zero)) * n))))
    (fromNat reals
      (factorial (suc ((suc (suc zero)) * n))))

cosineTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingPower reals n)
      (power reals x ((suc (suc zero)) * n)))
    (fromNat reals
      (factorial ((suc (suc zero)) * n)))

leibnizTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
leibnizTerm reals n =
  divide reals
    (alternatingPower reals n)
    (fromNat reals (suc ((suc (suc zero)) * n)))

SineValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
SineValue reals x value =
  SeriesHasSum reals (sineTerm reals x) value

CosineValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
CosineValue reals x value =
  SeriesHasSum reals (cosineTerm reals x) value

record PiValue
  {R : Set}
  (reals : CompleteOrderedField R)
  (value : R) : Set where
  field
    positive :
      StrictLess reals (zeroR reals) value
    leibniz-series :
      SeriesHasSum reals
        (leibnizTerm reals)
        (divide reals value
          (fromNat reals
            (suc (suc (suc (suc zero))))))

record SquareRootValue
  {R : Set}
  (reals : CompleteOrderedField R)
  (x root : R) : Set where
  field
    nonnegative :
      lessOrEqual reals (zeroR reals) root
    squares-to :
      square reals root == x

Subset : Set -> Set1
Subset A = A -> Set

Contained :
  {A : Set} ->
  Subset A ->
  Subset A ->
  Set
Contained {A} S T =
  (x : A) -> S x -> T x

Intersection :
  {A : Set} ->
  Subset A ->
  Subset A ->
  Subset A
Intersection S T x =
  Both (S x) (T x)

Difference :
  {A : Set} ->
  Subset A ->
  Subset A ->
  Subset A
Difference S T x =
  Both (S x) (Not (T x))

InPeriod :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
InPeriod reals pi x =
  Both
    (lessOrEqual reals (negate reals pi) x)
    (lessOrEqual reals x pi)

OpenInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
OpenInterval reals a b x =
  Both
    (StrictLess reals a x)
    (StrictLess reals x b)

intervalLength :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
intervalLength reals a b =
  maximum reals
    (zeroR reals)
    (subtract reals b a)

record CoverCost
  {R : Set}
  (reals : CompleteOrderedField R)
  (S : Subset R)
  (cost : R) : Set1 where
  field
    lower upper : Nat -> R
    covers :
      (x : R) ->
      S x ->
      Exists Nat
        (\ n -> OpenInterval reals (lower n) (upper n) x)
    cost-series :
      SeriesHasSum reals
        (\ n -> intervalLength reals (lower n) (upper n))
        cost

record OuterMeasureValue
  {R : Set}
  (reals : CompleteOrderedField R)
  (pi : R)
  (S : Subset R)
  (value : R) : Set1 where
  field
    inside-period :
      Contained S (InPeriod reals pi)
    nonnegative :
      lessOrEqual reals (zeroR reals) value
    lower-bound :
      (cost : R) ->
      CoverCost reals S cost ->
      lessOrEqual reals value cost
    greatest-lower-bound :
      (candidate : R) ->
      ((cost : R) ->
        CoverCost reals S cost ->
        lessOrEqual reals candidate cost) ->
      lessOrEqual reals candidate value

record LebesgueMeasurable
  {R : Set}
  (reals : CompleteOrderedField R)
  (pi : R)
  (S : Subset R) : Set1 where
  field
    inside-period :
      Contained S (InPeriod reals pi)
    caratheodory :
      (A : Subset R) ->
      (whole leftPart rightPart : R) ->
      OuterMeasureValue reals pi A whole ->
      OuterMeasureValue reals pi (Intersection A S) leftPart ->
      OuterMeasureValue reals pi (Difference A S) rightPart ->
      whole == add reals leftPart rightPart

OpenPreimageOnPeriod :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  (R -> R) ->
  R ->
  R ->
  Subset R
OpenPreimageOnPeriod reals pi f a b x =
  Both
    (InPeriod reals pi x)
    (OpenInterval reals a b (f x))

LebesgueMeasurableFunction :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  (R -> R) ->
  Set1
LebesgueMeasurableFunction {R} reals pi f =
  (a b : R) ->
  LebesgueMeasurable reals pi
    (OpenPreimageOnPeriod reals pi f a b)

positivePart :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R
positivePart reals f x =
  maximum reals (zeroR reals) (f x)

negativePart :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R
negativePart reals f x =
  maximum reals
    (zeroR reals)
    (negate reals (f x))

record NonnegativeSimpleBelow
  {R : Set}
  (reals : CompleteOrderedField R)
  (pi : R)
  (upperFunction simpleFunction : R -> R) : Set1 where
  field
    cutoff : Nat
    values : Nat -> R
    pieces : Nat -> Subset R

    values-nonnegative :
      (i : Nat) ->
      i <=N cutoff ->
      lessOrEqual reals (zeroR reals) (values i)
    pieces-measurable :
      (i : Nat) ->
      i <=N cutoff ->
      LebesgueMeasurable reals pi (pieces i)
    pieces-disjoint :
      (i j : Nat) ->
      i <=N cutoff ->
      j <=N cutoff ->
      i != j ->
      (x : R) ->
      Not (Both (pieces i x) (pieces j x))
    pieces-cover-period :
      (x : R) ->
      InPeriod reals pi x ->
      Exists Nat
        (\ i ->
          Both
            (i <=N cutoff)
            (pieces i x))
    represented-on-pieces :
      (i : Nat) ->
      i <=N cutoff ->
      (x : R) ->
      InPeriod reals pi x ->
      pieces i x ->
      simpleFunction x == values i
    nonnegative-and-below :
      (x : R) ->
      InPeriod reals pi x ->
      Both
        (lessOrEqual reals (zeroR reals) (simpleFunction x))
        (lessOrEqual reals (simpleFunction x) (upperFunction x))

record SimpleIntegralValue
  {R : Set}
  (reals : CompleteOrderedField R)
  (pi : R)
  (upperFunction simpleFunction : R -> R)
  (value : R) : Set1 where
  field
    simple :
      NonnegativeSimpleBelow
        reals pi upperFunction simpleFunction
    measures : Nat -> R
    piece-measure :
      (i : Nat) ->
      i <=N NonnegativeSimpleBelow.cutoff simple ->
      OuterMeasureValue reals pi
        (NonnegativeSimpleBelow.pieces simple i)
        (measures i)
    integral-equation :
      value ==
      sumThrough reals
        (\ i ->
          multiply reals
            (NonnegativeSimpleBelow.values simple i)
            (measures i))
        (NonnegativeSimpleBelow.cutoff simple)

record NonnegativeLebesgueIntegralValue
  {R : Set}
  (reals : CompleteOrderedField R)
  (pi : R)
  (function : R -> R)
  (value : R) : Set1 where
  field
    function-nonnegative :
      (x : R) ->
      InPeriod reals pi x ->
      lessOrEqual reals (zeroR reals) (function x)
    upper-bound :
      (simpleFunction : R -> R) ->
      (simpleValue : R) ->
      SimpleIntegralValue
        reals pi function simpleFunction simpleValue ->
      lessOrEqual reals simpleValue value
    least-upper-bound :
      (upper : R) ->
      ((simpleFunction : R -> R) ->
        (simpleValue : R) ->
        SimpleIntegralValue
          reals pi function simpleFunction simpleValue ->
        lessOrEqual reals simpleValue upper) ->
      lessOrEqual reals value upper

record LebesgueIntegralValue
  {R : Set}
  (reals : CompleteOrderedField R)
  (pi : R)
  (function : R -> R)
  (value : R) : Set1 where
  field
    measurable :
      LebesgueMeasurableFunction reals pi function
    positive-integral negative-integral : R
    positive-integral-value :
      NonnegativeLebesgueIntegralValue reals pi
        (positivePart reals function)
        positive-integral
    negative-integral-value :
      NonnegativeLebesgueIntegralValue reals pi
        (negativePart reals function)
        negative-integral
    integral-equation :
      value ==
      subtract reals positive-integral negative-integral

record LebesgueIntegrable
  {R : Set}
  (reals : CompleteOrderedField R)
  (pi : R)
  (function : R -> R) : Set1 where
  field
    integral : R
    integral-value :
      LebesgueIntegralValue reals pi function integral

record SquareIntegrable
  {R : Set}
  (reals : CompleteOrderedField R)
  (pi : R)
  (function : R -> R) : Set1 where
  field
    measurable :
      LebesgueMeasurableFunction reals pi function
    square-integrable :
      LebesgueIntegrable reals pi
        (\ x -> square reals (function x))

data Parity : Set where
  even odd : Parity

opposite : Parity -> Parity
opposite even = odd
opposite odd = even

parity : Nat -> Parity
parity zero = even
parity (suc n) = opposite (parity n)

half : Nat -> Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

TrigonometricBasisValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R ->
  R ->
  Set
TrigonometricBasisValue {R} reals pi zero x value =
  Exists R
    (\ root ->
      Both
        (SquareRootValue reals
          (multiply reals
            (fromNat reals (suc (suc zero)))
            pi)
          root)
        (value == divide reals (oneR reals) root))
TrigonometricBasisValue {R} reals pi (suc n) x value
  with parity (suc n)
... | odd =
  Exists R
    (\ sineValue ->
      Exists R
        (\ root ->
          Both
            (SineValue reals
              (multiply reals
                (fromNat reals (suc (half (suc n))))
                x)
              sineValue)
            (Both
              (SquareRootValue reals pi root)
              (value == divide reals sineValue root))))
... | even =
  Exists R
    (\ cosineValue ->
      Exists R
        (\ root ->
          Both
            (CosineValue reals
              (multiply reals
                (fromNat reals (half (suc n)))
                x)
              cosineValue)
            (Both
              (SquareRootValue reals pi root)
              (value == divide reals cosineValue root))))

fourierPartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R -> R) ->
  (Nat -> R) ->
  Nat ->
  R ->
  R
fourierPartialSum reals basis coefficients n x =
  sumThrough reals
    (\ i ->
      multiply reals
        (coefficients i)
        (basis i x))
    n

record L2NormValue
  {R : Set}
  (reals : CompleteOrderedField R)
  (pi : R)
  (function : R -> R)
  (value : R) : Set1 where
  field
    squared-integral : R
    squared-integral-value :
      LebesgueIntegralValue reals pi
        (\ x -> square reals (function x))
        squared-integral
    square-root-value :
      SquareRootValue reals squared-integral value

record FourierExpansionConverges
  {R : Set}
  (reals : CompleteOrderedField R)
  (pi : R)
  (function : R -> R) : Set1 where
  field
    basis : Nat -> R -> R
    basis-values :
      (n : Nat) ->
      (x : R) ->
      TrigonometricBasisValue reals pi n x (basis n x)

    coefficients : Nat -> R
    coefficient-values :
      (n : Nat) ->
      LebesgueIntegralValue reals pi
        (\ x -> multiply reals (basis n x) (function x))
        (coefficients n)

    errors : Nat -> R
    error-values :
      (n : Nat) ->
      L2NormValue reals pi
        (\ x ->
          subtract reals
            (function x)
            (fourierPartialSum reals basis coefficients n x))
        (errors n)
    errors-converge-to-zero :
      ConvergesTo reals errors (zeroR reals)

record FourierSeriesStatement
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    pi : R
    pi-value : PiValue reals pi
    l2-convergence :
      (function : R -> R) ->
      SquareIntegrable reals pi function ->
      FourierExpansionConverges reals pi function

fourier-series : Set1
fourier-series =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  FourierSeriesStatement reals
