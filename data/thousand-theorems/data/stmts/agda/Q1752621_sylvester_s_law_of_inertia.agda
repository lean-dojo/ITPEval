-- Statement-only formalization of thousand-theorems corpus artifact
-- thousand-theorems__agda__Q1752621, "Sylvester's law of inertia": every
-- quadratic form on a finite-dimensional real vector space is linearly
-- equivalent to a weighted sum of squares with weights -1, 0, or 1. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Q1752621_sylvester_s_law_of_inertia where

open import Agda.Primitive using (Level; lsuc; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

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

record Iff (A B : Set) : Set where
  field
    forward  : A -> B
    backward : B -> A

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
      Exists R (\ upper -> (x : R) -> P x -> lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Vector :
  Set ->
  Nat ->
  Set
Vector R n =
  Fin n -> R

VectorEqual :
  {R : Set} ->
  {n : Nat} ->
  Vector R n ->
  Vector R n ->
  Set
VectorEqual {n = n} x y =
  (i : Fin n) -> x i == y i

vectorZero :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n
vectorZero reals i =
  zeroR reals

vectorAdd :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Vector R n
vectorAdd reals x y i =
  addR reals (x i) (y i)

vectorScale :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  R ->
  Vector R n ->
  Vector R n
vectorScale reals scalar x i =
  multiplyR reals scalar (x i)

sumFin :
  {R : Set} ->
  CompleteOrderedField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} term =
  zeroR reals
sumFin reals {suc n} term =
  addR reals
    (term fzero)
    (sumFin reals (\ i -> term (fsuc i)))

record VectorSpace
  {m : Level}
  {R : Set}
  (reals : CompleteOrderedField R)
  (M-carrier : Set m) : Set (lsuc m) where
  field
    zeroM : M-carrier
    addM : M-carrier -> M-carrier -> M-carrier
    negateM : M-carrier -> M-carrier
    scaleM : R -> M-carrier -> M-carrier

    add-commutativeM :
      (x y : M-carrier) ->
      addM x y == addM y x
    add-associativeM :
      (x y z : M-carrier) ->
      addM (addM x y) z == addM x (addM y z)
    add-zeroM :
      (x : M-carrier) ->
      addM x zeroM == x
    add-inverseM :
      (x : M-carrier) ->
      addM x (negateM x) == zeroM

    scale-oneM :
      (x : M-carrier) ->
      scaleM (oneR reals) x == x
    scale-associativeM :
      (a b : R) ->
      (x : M-carrier) ->
      scaleM (multiplyR reals a b) x ==
      scaleM a (scaleM b x)
    scale-addM :
      (a : R) ->
      (x y : M-carrier) ->
      scaleM a (addM x y) ==
      addM (scaleM a x) (scaleM a y)
    add-scaleM :
      (a b : R) ->
      (x : M-carrier) ->
      scaleM (addR reals a b) x ==
      addM (scaleM a x) (scaleM b x)

open VectorSpace

record LinearEquivalence
  {m : Level}
  {R : Set}
  {M : Set m}
  (reals : CompleteOrderedField R)
  (space : VectorSpace reals M)
  (n : Nat) : Set (lsuc m) where
  field
    coordinates :
      M -> Vector R n
    rebuild :
      Vector R n -> M
    coordinates-after-rebuild :
      (x : Vector R n) ->
      VectorEqual (coordinates (rebuild x)) x
    rebuild-after-coordinates :
      (x : M) ->
      rebuild (coordinates x) == x
    coordinates-add :
      (x y : M) ->
      VectorEqual
        (coordinates (addM space x y))
        (vectorAdd reals (coordinates x) (coordinates y))
    coordinates-scale :
      (a : R) ->
      (x : M) ->
      VectorEqual
        (coordinates (scaleM space a x))
        (vectorScale reals a (coordinates x))

record FiniteDimensional
  {m : Level}
  {R : Set}
  {M : Set m}
  (reals : CompleteOrderedField R)
  (space : VectorSpace reals M) : Set (lsuc m) where
  field
    dimension :
      Nat
    linear-coordinates :
      LinearEquivalence reals space dimension

open FiniteDimensional

record QuadraticForm
  {m : Level}
  {R : Set}
  {M : Set m}
  (reals : CompleteOrderedField R)
  (space : VectorSpace reals M) : Set (lsuc m) where
  field
    evaluate :
      M -> R
    associated :
      M -> M -> R
    associated-add-left :
      (x y z : M) ->
      associated (addM space x y) z ==
      addR reals (associated x z) (associated y z)
    associated-scale-left :
      (a : R) ->
      (x y : M) ->
      associated (scaleM space a x) y ==
      multiplyR reals a (associated x y)
    associated-add-right :
      (x y z : M) ->
      associated x (addM space y z) ==
      addR reals (associated x y) (associated x z)
    associated-scale-right :
      (a : R) ->
      (x y : M) ->
      associated x (scaleM space a y) ==
      multiplyR reals a (associated x y)
    associated-symmetric :
      (x y : M) ->
      associated x y == associated y x
    evaluate-associated :
      (x : M) ->
      evaluate x == associated x x

open QuadraticForm

weightedSumSquares :
  {R : Set} ->
  CompleteOrderedField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  Vector R n ->
  R
weightedSumSquares reals weights x =
  sumFin reals
    (\ i ->
      multiplyR reals
        (weights i)
        (multiplyR reals (x i) (x i)))

record Equivalent
  {m : Level}
  {R : Set}
  {M : Set m}
  (reals : CompleteOrderedField R)
  (space : VectorSpace reals M)
  (quadratic : QuadraticForm reals space)
  (n : Nat)
  (weights : Fin n -> R) : Set (lsuc m) where
  field
    coordinate-change :
      LinearEquivalence reals space n
    preserves-quadratic-form :
      (x : M) ->
      evaluate quadratic x ==
      weightedSumSquares reals weights
        (LinearEquivalence.coordinates coordinate-change x)

WeightIsOneZeroNegOne :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
WeightIsOneZeroNegOne reals weight =
  Either
    (weight == negateR reals (oneR reals))
    (Either
      (weight == zeroR reals)
      (weight == oneR reals))

record SylvesterNormalForm
  {m : Level}
  {R : Set}
  {M : Set m}
  (reals : CompleteOrderedField R)
  (space : VectorSpace reals M)
  (finite-dimensional : FiniteDimensional reals space)
  (quadratic : QuadraticForm reals space) : Set (lsuc m) where
  field
    weights :
      Fin (dimension finite-dimensional) -> R
    weights-are-one-zero-neg-one :
      (i : Fin (dimension finite-dimensional)) ->
      WeightIsOneZeroNegOne reals (weights i)
    equivalent-weighted-sum-squares :
      Equivalent reals space quadratic
        (dimension finite-dimensional) weights

sylvesters-law-of-inertia : Setω
sylvesters-law-of-inertia =
  {m : Level} ->
  (R : Set) ->
  (M : Set m) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (space : VectorSpace reals M) ->
  (finite-dimensional : FiniteDimensional reals space) ->
  (quadratic : QuadraticForm reals space) ->
  SylvesterNormalForm reals space finite-dimensional quadratic
