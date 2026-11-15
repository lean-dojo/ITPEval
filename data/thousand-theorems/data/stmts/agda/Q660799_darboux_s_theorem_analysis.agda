-- Statement-only formalization of thousand-theorems corpus artifact Q660799,
-- "Darboux's theorem (analysis)": derivatives take intermediate values, so
-- their images on order-connected or convex real sets remain order-connected
-- or convex. This file contains no proof.

{-# OPTIONS --safe #-}

module Q660799_darboux_s_theorem_analysis where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_

data Bottom : Set where

data Top : Set where
  trivial : Top

Not : Set -> Set
Not proposition =
  proposition -> Bottom

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
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNat-multiplicationR :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
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
CloseTo reals center radius point =
  Both
    (StrictLess reals (subtractR reals center radius) point)
    (StrictLess reals point (addR reals center radius))

ClosedInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
ClosedInterval reals lower upper point =
  Both
    (lessOrEqualR reals lower point)
    (lessOrEqualR reals point upper)

OpenInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
OpenInterval reals lower upper point =
  Both
    (StrictLess reals lower point)
    (StrictLess reals point upper)

Image :
  {R : Set} ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  Set
Image {R} function domain output =
  Exists R
    (\ input ->
      Both
        (domain input)
        (function input == output))

OrdConnected :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> Set) ->
  Set
OrdConnected {R} reals domain =
  (lower upper middle : R) ->
  domain lower ->
  domain upper ->
  lessOrEqualR reals lower middle ->
  lessOrEqualR reals middle upper ->
  domain middle

Convex :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> Set) ->
  Set
Convex {R} reals domain =
  (x y : R) ->
  domain x ->
  domain y ->
  (a b : R) ->
  lessOrEqualR reals (zeroR reals) a ->
  lessOrEqualR reals (zeroR reals) b ->
  addR reals a b == oneR reals ->
  domain
    (addR reals
      (multiplyR reals a x)
      (multiplyR reals b y))

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

HasDerivWithinAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  (R -> Set) ->
  R ->
  Set
HasDerivWithinAt {R} reals function derivative domain point =
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

HasDerivAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  Set
HasDerivAt {R} reals function derivative point =
  HasDerivWithinAt reals function derivative (\ _ -> Top) point

DifferentiableWithinOn :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  Set
DifferentiableWithinOn {R} reals function domain =
  (point : R) ->
  domain point ->
  Exists R
    (\ derivative ->
      HasDerivWithinAt reals function derivative domain point)

DifferentiableAtOn :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  Set
DifferentiableAtOn {R} reals function domain =
  (point : R) ->
  domain point ->
  Exists R
    (\ derivative ->
      HasDerivAt reals function derivative point)

UniqueDerivWithinAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  R ->
  Set
UniqueDerivWithinAt {R} reals function domain point derivative =
  Both
    (HasDerivWithinAt reals function derivative domain point)
    ((other : R) ->
      HasDerivWithinAt reals function other domain point ->
      other == derivative)

HasUniqueDerivWithinAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  Set
HasUniqueDerivWithinAt {R} reals function domain point =
  Exists R
    (\ derivative ->
      UniqueDerivWithinAt reals function domain point derivative)

TotalizedDerivWithinValue :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  R ->
  Set
TotalizedDerivWithinValue {R} reals function domain point derivative =
  Either
    (Both
      (HasDerivWithinAt reals function (zeroR reals) domain point)
      (derivative == zeroR reals))
    (Either
      (Both
        (Not
          (HasDerivWithinAt
            reals function (zeroR reals) domain point))
        (UniqueDerivWithinAt
          reals function domain point derivative))
      (Both
        (Not
          (Exists R
            (\ candidate ->
              HasDerivWithinAt
                reals function candidate domain point)))
        (derivative == zeroR reals)))

UniqueDerivAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  Set
UniqueDerivAt {R} reals function point derivative =
  Both
    (HasDerivAt reals function derivative point)
    ((other : R) ->
      HasDerivAt reals function other point ->
      other == derivative)

HasUniqueDerivAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  Set
HasUniqueDerivAt {R} reals function point =
  Exists R
    (\ derivative ->
      UniqueDerivAt reals function point derivative)

TotalizedDerivValue :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  Set
TotalizedDerivValue {R} reals function point derivative =
  Either
    (Both
      (HasDerivAt reals function (zeroR reals) point)
      (derivative == zeroR reals))
    (Either
      (Both
        (Not (HasDerivAt reals function (zeroR reals) point))
        (UniqueDerivAt reals function point derivative))
      (Both
        (Not
          (Exists R
            (\ candidate ->
              HasDerivAt reals function candidate point)))
        (derivative == zeroR reals)))

DerivWithinImage :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  Set
DerivWithinImage {R} reals function domain output =
  Exists R
    (\ point ->
      Both
        (domain point)
        (TotalizedDerivWithinValue
          reals function domain point output))

DerivImage :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  Set
DerivImage {R} reals function domain output =
  Exists R
    (\ point ->
      Both
        (domain point)
        (TotalizedDerivValue reals function point output))

exists-hasDerivWithinAt-eq-of-gt-of-lt : Set2
exists-hasDerivWithinAt-eq-of-gt-of-lt =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f f' : R -> R) ->
  (a b : R) ->
  lessOrEqualR reals a b ->
  ((x : R) ->
    ClosedInterval reals a b x ->
    HasDerivWithinAt reals f (f' x)
      (ClosedInterval reals a b) x) ->
  (m : R) ->
  StrictLess reals (f' a) m ->
  StrictLess reals m (f' b) ->
  Exists R
    (\ c ->
      Both
        (OpenInterval reals a b c)
        (f' c == m))

exists-hasDerivWithinAt-eq-of-lt-of-gt : Set2
exists-hasDerivWithinAt-eq-of-lt-of-gt =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f f' : R -> R) ->
  (a b : R) ->
  lessOrEqualR reals a b ->
  ((x : R) ->
    ClosedInterval reals a b x ->
    HasDerivWithinAt reals f (f' x)
      (ClosedInterval reals a b) x) ->
  (m : R) ->
  StrictLess reals m (f' a) ->
  StrictLess reals (f' b) m ->
  Exists R
    (\ c ->
      Both
        (OpenInterval reals a b c)
        (f' c == m))

ordConnected-image-hasDerivWithinAt : Set2
ordConnected-image-hasDerivWithinAt =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f f' : R -> R) ->
  (domain : R -> Set) ->
  OrdConnected reals domain ->
  ((x : R) ->
    domain x ->
    HasDerivWithinAt reals f (f' x) domain x) ->
  OrdConnected reals (Image f' domain)

ordConnected-image-derivWithin : Set2
ordConnected-image-derivWithin =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f : R -> R) ->
  (domain : R -> Set) ->
  OrdConnected reals domain ->
  DifferentiableWithinOn reals f domain ->
  OrdConnected reals (DerivWithinImage reals f domain)

ordConnected-image-deriv : Set2
ordConnected-image-deriv =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f : R -> R) ->
  (domain : R -> Set) ->
  OrdConnected reals domain ->
  DifferentiableAtOn reals f domain ->
  OrdConnected reals (DerivImage reals f domain)

convex-image-hasDerivWithinAt : Set2
convex-image-hasDerivWithinAt =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f f' : R -> R) ->
  (domain : R -> Set) ->
  Convex reals domain ->
  ((x : R) ->
    domain x ->
    HasDerivWithinAt reals f (f' x) domain x) ->
  Convex reals (Image f' domain)

convex-image-derivWithin : Set2
convex-image-derivWithin =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f : R -> R) ->
  (domain : R -> Set) ->
  Convex reals domain ->
  DifferentiableWithinOn reals f domain ->
  Convex reals (DerivWithinImage reals f domain)

convex-image-deriv : Set2
convex-image-deriv =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f : R -> R) ->
  (domain : R -> Set) ->
  Convex reals domain ->
  DifferentiableAtOn reals f domain ->
  Convex reals (DerivImage reals f domain)

exists-hasDerivWithinAt-eq-of-ge-of-le : Set2
exists-hasDerivWithinAt-eq-of-ge-of-le =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f f' : R -> R) ->
  (a b : R) ->
  lessOrEqualR reals a b ->
  ((x : R) ->
    ClosedInterval reals a b x ->
    HasDerivWithinAt reals f (f' x)
      (ClosedInterval reals a b) x) ->
  (m : R) ->
  lessOrEqualR reals (f' a) m ->
  lessOrEqualR reals m (f' b) ->
  Exists R
    (\ c ->
      Both
        (ClosedInterval reals a b c)
        (f' c == m))

exists-hasDerivWithinAt-eq-of-le-of-ge : Set2
exists-hasDerivWithinAt-eq-of-le-of-ge =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f f' : R -> R) ->
  (a b : R) ->
  lessOrEqualR reals a b ->
  ((x : R) ->
    ClosedInterval reals a b x ->
    HasDerivWithinAt reals f (f' x)
      (ClosedInterval reals a b) x) ->
  (m : R) ->
  lessOrEqualR reals (f' a) m ->
  lessOrEqualR reals m (f' b) ->
  Exists R
    (\ c ->
      Both
        (ClosedInterval reals a b c)
        (f' c == m))
