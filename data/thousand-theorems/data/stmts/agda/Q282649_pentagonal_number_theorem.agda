-- Statement-only formalization of thousand-theorems corpus artifact Q282649,
-- "Pentagonal number theorem": over an arbitrary commutative ring with an
-- arbitrary coefficient topology, the unordered finite-subset product net
-- of (1 - X^(n+1)) converges coefficientwise to the generalized pentagonal
-- power series. This file contains no proof.

{-# OPTIONS --safe #-}

module Q282649_pentagonal_number_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infixr 3 _×_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} →
  Set a →
  Set a
Not {a} proposition =
  proposition → Bottom {a}

record Top {a : Level} : Set a where
  constructor truth

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A → Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

Predicate :
  {a : Level} →
  Set a →
  Set (lsuc a)
Predicate {a} A =
  A → Set a

Whole :
  {a : Level} →
  {A : Set a} →
  Predicate A
Whole _ =
  Top

Intersection :
  {a : Level} →
  {A : Set a} →
  Predicate A →
  Predicate A →
  Predicate A
Intersection P Q x =
  P x × Q x

Subset :
  {a : Level} →
  {A : Set a} →
  Predicate A →
  Predicate A →
  Set a
Subset {A = A} P Q =
  (x : A) →
  P x →
  Q x

record NeighborhoodRefinement
  {a : Level}
  {A : Set a}
  (near : A → Predicate A → Set a)
  (x : A)
  (U : Predicate A) :
  Set (lsuc a) where

  field
    refinement :
      Predicate A

    refinement-near :
      near x refinement

    refinement-stays-near :
      (y : A) →
      refinement y →
      near y U

record TopologicalSpace
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    neighborhood :
      A →
      Predicate A →
      Set a

    neighborhood-contains :
      (x : A) →
      (U : Predicate A) →
      neighborhood x U →
      U x

    neighborhood-whole :
      (x : A) →
      neighborhood x Whole

    neighborhood-upward :
      (x : A) →
      (U V : Predicate A) →
      neighborhood x U →
      Subset U V →
      neighborhood x V

    neighborhood-intersection :
      (x : A) →
      (U V : Predicate A) →
      neighborhood x U →
      neighborhood x V →
      neighborhood x (Intersection U V)

    neighborhood-local :
      (x : A) →
      (U : Predicate A) →
      neighborhood x U →
      NeighborhoodRefinement neighborhood x U

open TopologicalSpace

record CommutativeRing
  {a : Level}
  (R : Set a) :
  Set a where

  field
    zeroR oneR :
      R

    addR multiplyR :
      R →
      R →
      R

    negateR :
      R →
      R

    add-commutative :
      (x y : R) →
      addR x y ≡ addR y x

    add-associative :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)

    add-zero-left :
      (x : R) →
      addR zeroR x ≡ x

    add-zero-right :
      (x : R) →
      addR x zeroR ≡ x

    add-inverse-left :
      (x : R) →
      addR (negateR x) x ≡ zeroR

    add-inverse-right :
      (x : R) →
      addR x (negateR x) ≡ zeroR

    multiply-commutative :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x

    multiply-associative :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)

    multiply-one-left :
      (x : R) →
      multiplyR oneR x ≡ x

    multiply-one-right :
      (x : R) →
      multiplyR x oneR ≡ x

    distribute-left :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)

    distribute-right :
      (x y z : R) →
      multiplyR (addR x y) z ≡
      addR (multiplyR x z) (multiplyR y z)

open CommutativeRing

data Member (x : Nat) : List Nat → Set where
  at-head :
    {xs : List Nat} →
    Member x (x ∷ xs)

  in-tail :
    {y : Nat} →
    {xs : List Nat} →
    Member x xs →
    Member x (y ∷ xs)

data NoDuplicates : List Nat → Set where
  no-duplicates-empty :
    NoDuplicates []

  no-duplicates-cons :
    {x : Nat} →
    {xs : List Nat} →
    Not (Member x xs) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

record FiniteSubsetNat : Set where
  field
    elements      : List Nat
    no-duplicates : NoDuplicates elements

open FiniteSubsetNat

FiniteSubsetIncluded :
  FiniteSubsetNat →
  FiniteSubsetNat →
  Set
FiniteSubsetIncluded child parent =
  (n : Nat) →
  Member n (elements child) →
  Member n (elements parent)

EventuallyFiniteSubsets :
  {p : Level} →
  (FiniteSubsetNat → Set p) →
  Set p
EventuallyFiniteSubsets P =
  Exists FiniteSubsetNat
    (λ cutoff →
      (subset : FiniteSubsetNat) →
      FiniteSubsetIncluded cutoff subset →
      P subset)

PowerSeries :
  {a : Level} →
  Set a →
  Set a
PowerSeries R =
  Nat → R

subtractR :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  R →
  R →
  R
subtractR ring x y =
  addR ring x (negateR ring y)

sumUpTo :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  (Nat → R) →
  Nat →
  R
sumUpTo ring summand zero =
  summand zero
sumUpTo ring summand (suc n) =
  addR ring
    (sumUpTo ring summand n)
    (summand (suc n))

oneSeries :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  PowerSeries R
oneSeries ring zero =
  oneR ring
oneSeries ring (suc n) =
  zeroR ring

xSeries :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  PowerSeries R
xSeries ring zero =
  zeroR ring
xSeries ring (suc zero) =
  oneR ring
xSeries ring (suc (suc n)) =
  zeroR ring

addSeries :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  PowerSeries R →
  PowerSeries R →
  PowerSeries R
addSeries ring left right n =
  addR ring (left n) (right n)

negateSeries :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  PowerSeries R →
  PowerSeries R
negateSeries ring series n =
  negateR ring (series n)

subtractSeries :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  PowerSeries R →
  PowerSeries R →
  PowerSeries R
subtractSeries ring left right =
  addSeries ring left (negateSeries ring right)

multiplySeries :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  PowerSeries R →
  PowerSeries R →
  PowerSeries R
multiplySeries ring left right n =
  sumUpTo ring
    (λ i →
      multiplyR ring
        (left i)
        (right (n - i)))
    n

powerSeries :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  PowerSeries R →
  Nat →
  PowerSeries R
powerSeries ring series zero =
  oneSeries ring
powerSeries ring series (suc exponent) =
  multiplySeries ring
    (powerSeries ring series exponent)
    series

oneMinusXPow :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  Nat →
  PowerSeries R
oneMinusXPow ring n =
  subtractSeries ring
    (oneSeries ring)
    (powerSeries ring (xSeries ring) (suc n))

productSeriesList :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  (Nat → PowerSeries R) →
  List Nat →
  PowerSeries R
productSeriesList ring factors [] =
  oneSeries ring
productSeriesList ring factors (n ∷ ns) =
  multiplySeries ring
    (factors n)
    (productSeriesList ring factors ns)

finiteSubsetProduct :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  (Nat → PowerSeries R) →
  FiniteSubsetNat →
  PowerSeries R
finiteSubsetProduct ring factors subset =
  productSeriesList ring factors (elements subset)

half :
  Nat →
  Nat
half zero =
  zero
half (suc zero) =
  zero
half (suc (suc n)) =
  suc (half n)

threeTimes :
  Nat →
  Nat
threeTimes n =
  n + (n + n)

pentagonal :
  Int →
  Nat
pentagonal (pos n) =
  half (n * (threeTimes n - suc zero))
pentagonal (negsuc n) =
  half ((suc n) * suc (threeTimes (suc n)))

negOnePowNat :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  Nat →
  R
negOnePowNat ring zero =
  oneR ring
negOnePowNat ring (suc n) =
  negateR ring (negOnePowNat ring n)

negOnePowInt :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  Int →
  R
negOnePowInt ring (pos n) =
  negOnePowNat ring n
negOnePowInt ring (negsuc n) =
  negOnePowNat ring (suc n)

natEqual :
  Nat →
  Nat →
  Bool
natEqual zero zero =
  true
natEqual zero (suc n) =
  false
natEqual (suc m) zero =
  false
natEqual (suc m) (suc n) =
  natEqual m n

data Maybe
  {a : Level}
  (A : Set a) :
  Set a where

  nothing :
    Maybe A

  just :
    A →
    Maybe A

firstJust :
  {a : Level} →
  {A : Set a} →
  Maybe A →
  Maybe A →
  Maybe A
firstJust (just x) other =
  just x
firstJust nothing other =
  other

coefficientAtCandidate :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  Nat →
  Int →
  Maybe R
coefficientAtCandidate ring target k
  with natEqual (pentagonal k) target
... | true =
  just (negOnePowInt ring k)
... | false =
  nothing

searchPentagonalCoefficient :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  Nat →
  Nat →
  Maybe R
searchPentagonalCoefficient ring target zero =
  firstJust
    (coefficientAtCandidate ring target (pos zero))
    (coefficientAtCandidate ring target (negsuc zero))
searchPentagonalCoefficient ring target (suc bound) =
  firstJust
    (coefficientAtCandidate ring target (pos (suc bound)))
    (firstJust
      (coefficientAtCandidate ring target (negsuc (suc bound)))
      (searchPentagonalCoefficient ring target bound))

pentagonalSeries :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  PowerSeries R
pentagonalSeries ring n
  with searchPentagonalCoefficient ring n n
... | just coefficient =
  coefficient
... | nothing =
  zeroR ring

PiTopologyTendsto :
  {a : Level} →
  {R : Set a} →
  TopologicalSpace R →
  (FiniteSubsetNat → PowerSeries R) →
  PowerSeries R →
  Set (lsuc a)
PiTopologyTendsto {R = R} topology values limit =
  (degree : Nat) →
  (U : Predicate R) →
  neighborhood topology (limit degree) U →
  EventuallyFiniteSubsets
    (λ subset →
      U (values subset degree))

HasProd :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  TopologicalSpace R →
  (Nat → PowerSeries R) →
  PowerSeries R →
  Set (lsuc a)
HasProd ring topology factors limit =
  PiTopologyTendsto topology
    (finiteSubsetProduct ring factors)
    limit

-- Lean: PowerSeries.WithPiTopology.hasProd_one_sub_X_pow
pentagonal-number-theorem :
  {a : Level} →
  Set (lsuc a)
pentagonal-number-theorem {a} =
  (R : Set a) →
  (ring : CommutativeRing R) →
  (topology : TopologicalSpace R) →
  HasProd ring topology
    (oneMinusXPow ring)
    (pentagonalSeries ring)
