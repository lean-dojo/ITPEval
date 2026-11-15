-- Statement-only formalization of thousand-theorems corpus artifact Q1137206,
-- "Taylor's theorem": the Lagrange and Cauchy forms of the remainder for a
-- real function with the stated closed-interval smoothness assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1137206_taylor_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_ _<N_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record Exists1 (A : Set) (P : A -> Set1) : Set1 where
  constructor witness1
  field
    value1    : A
    property1 : P value1

data _<N_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero <N suc n
  succ<succ : {m n : Nat} -> m <N n -> suc m <N suc n

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  succ<=succ : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) -> addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) -> addR x zeroR == x
    add-inverseR :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) -> multiplyR x oneR == x
    multiply-zeroR :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexiveR :
      (x : R) -> lessOrEqualR x x
    order-transitiveR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-totalR :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-orderR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-additionR :
      (m n : Nat) ->
      fromNatR (Agda.Builtin.Nat._+_ m n) ==
      addR (fromNatR m) (fromNatR n)
    fromNat-multiplicationR :
      (m n : Nat) ->
      fromNatR (m * n) ==
      multiplyR (fromNatR m) (fromNatR n)
    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) ->
              P x ->
              lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) ->
                P x ->
                lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) : Set1 where
  field
    forwardR :
      R -> S
    backwardR :
      S -> R
    forward-after-backwardR :
      (y : S) -> forwardR (backwardR y) == y
    backward-after-forwardR :
      (x : R) -> backwardR (forwardR x) == x
    forward-zeroR :
      forwardR (zeroR source) == zeroR target
    forward-oneR :
      forwardR (oneR source) == oneR target
    forward-addR :
      (x y : R) ->
      forwardR (addR source x y) ==
      addR target (forwardR x) (forwardR y)
    forward-multiplyR :
      (x y : R) ->
      forwardR (multiplyR source x y) ==
      multiplyR target (forwardR x) (forwardR y)
    forward-negateR :
      (x : R) ->
      forwardR (negateR source x) ==
      negateR target (forwardR x)
    forward-reciprocalR :
      (x : R) ->
      forwardR (reciprocalR source x) ==
      reciprocalR target (forwardR x)
    forward-fromNatR :
      (n : Nat) ->
      forwardR (fromNatR source n) == fromNatR target n
    forward-orderR :
      (x y : R) ->
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) : Set2 where
  field
    equivalent-complete-ordered-field :
      (S : Set) ->
      (other : CompleteOrderedField S) ->
      CompleteOrderedFieldEquivalence reals other

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

divideR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divideR reals x y =
  multiplyR reals x (reciprocalR reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  Both
    (StrictLess reals (subtractR reals center radius) x)
    (StrictLess reals x (addR reals center radius))

InClosedInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
InClosedInterval reals lower upper point =
  Both
    (lessOrEqualR reals lower point)
    (lessOrEqualR reals point upper)

InOpenInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
InOpenInterval reals lower upper point =
  Both
    (StrictLess reals lower point)
    (StrictLess reals point upper)

ContinuousWithinAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  Set
ContinuousWithinAt {R} reals function domain point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((y : R) ->
          domain y ->
          CloseTo reals point delta y ->
          CloseTo reals (function point) epsilon (function y)))

ContinuousOn :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  Set
ContinuousOn {R} reals function domain =
  (point : R) ->
  domain point ->
  ContinuousWithinAt reals function domain point

differenceQuotient :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  R
differenceQuotient reals function point y =
  divideR reals
    (subtractR reals (function y) (function point))
    (subtractR reals y point)

DerivativeWithinAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  R ->
  Set
DerivativeWithinAt {R} reals function domain point derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((y : R) ->
          domain y ->
          CloseTo reals point delta y ->
          y != point ->
          CloseTo reals derivative epsilon
            (differenceQuotient reals function point y)))

DerivativeAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals function point derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((y : R) ->
          CloseTo reals point delta y ->
          y != point ->
          CloseTo reals derivative epsilon
            (differenceQuotient reals function point y)))

record RepresentsTaylorDerivatives
  {R : Set}
  (reals : CompleteOrderedField R)
  (function : R -> R)
  (center endpoint : R)
  (order : Nat)
  (derivatives : Nat -> R -> R) : Set1 where
  field
    zeroth-derivative :
      (point : R) ->
      InClosedInterval reals center endpoint point ->
      derivatives zero point == function point

    continuous-through-order :
      (k : Nat) ->
      k <=N order ->
      ContinuousOn reals
        (derivatives k)
        (InClosedInterval reals center endpoint)

    derivative-through-predecessors :
      (k : Nat) ->
      k <N order ->
      (point : R) ->
      InClosedInterval reals center endpoint point ->
      DerivativeWithinAt reals
        (derivatives k)
        (InClosedInterval reals center endpoint)
        point
        (derivatives (suc k) point)

    top-derivative-on-interior :
      (point : R) ->
      InOpenInterval reals center endpoint point ->
      DerivativeAt reals
        (derivatives order)
        point
        (derivatives (suc order) point)

open RepresentsTaylorDerivatives

TaylorRegularity :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (function : R -> R) ->
  (center endpoint : R) ->
  Nat ->
  Set1
TaylorRegularity reals function center endpoint order =
  Exists1
    (Nat -> _ -> _)
    (RepresentsTaylorDerivatives
      reals function center endpoint order)

powerR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
powerR reals x zero =
  oneR reals
powerR reals x (suc n) =
  multiplyR reals (powerR reals x n) x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals term zero =
  zeroR reals
sumFirst reals term (suc n) =
  addR reals
    (sumFirst reals term n)
    (term n)

taylorTerm :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (Nat -> R -> R) ->
  R ->
  R ->
  Nat ->
  R
taylorTerm reals derivatives center point k =
  multiplyR reals
    (divideR reals
      (derivatives k center)
      (fromNatR reals (factorial k)))
    (powerR reals (subtractR reals point center) k)

taylorPolynomial :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (Nat -> R -> R) ->
  R ->
  R ->
  Nat ->
  R
taylorPolynomial reals derivatives center point order =
  sumFirst reals
    (taylorTerm reals derivatives center point)
    (suc order)

lagrangeRemainder :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (Nat -> R -> R) ->
  R ->
  R ->
  Nat ->
  R ->
  R
lagrangeRemainder reals derivatives center endpoint order intermediate =
  divideR reals
    (multiplyR reals
      (derivatives (suc order) intermediate)
      (powerR reals
        (subtractR reals endpoint center)
        (suc order)))
    (fromNatR reals (factorial (suc order)))

cauchyRemainder :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (Nat -> R -> R) ->
  R ->
  R ->
  Nat ->
  R ->
  R
cauchyRemainder reals derivatives center endpoint order intermediate =
  multiplyR reals
    (divideR reals
      (multiplyR reals
        (derivatives (suc order) intermediate)
        (powerR reals
          (subtractR reals endpoint intermediate)
          order))
      (fromNatR reals (factorial order)))
    (subtractR reals endpoint center)

taylor-mean-remainder-lagrange : Set2
taylor-mean-remainder-lagrange =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (function : R -> R) ->
  (center endpoint : R) ->
  (order : Nat) ->
  StrictLess reals center endpoint ->
  (regularity :
    TaylorRegularity reals function center endpoint order) ->
  Exists R
    (\ intermediate ->
      Both
        (InOpenInterval reals center endpoint intermediate)
        (subtractR reals
          (function endpoint)
          (taylorPolynomial reals
            (Exists1.value1 regularity)
            center endpoint order)
        ==
        lagrangeRemainder reals
          (Exists1.value1 regularity)
          center endpoint order intermediate))

taylor-mean-remainder-cauchy : Set2
taylor-mean-remainder-cauchy =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (function : R -> R) ->
  (center endpoint : R) ->
  (order : Nat) ->
  StrictLess reals center endpoint ->
  (regularity :
    TaylorRegularity reals function center endpoint order) ->
  Exists R
    (\ intermediate ->
      Both
        (InOpenInterval reals center endpoint intermediate)
        (subtractR reals
          (function endpoint)
          (taylorPolynomial reals
            (Exists1.value1 regularity)
            center endpoint order)
        ==
        cauchyRemainder reals
          (Exists1.value1 regularity)
          center endpoint order intermediate))
