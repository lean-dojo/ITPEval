-- Statement-only formalization of thousand-theorems corpus artifact Q3527219,
-- "Weierstrass preparation theorem": a power series over a complete local
-- commutative ring whose residue-field image is nonzero factors as a
-- distinguished polynomial times a unit power series. This file contains no proof.

{-# OPTIONS --safe #-}

module Q3527219_weierstrass_preparation_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_ _≤_ _<_
infixr 3 _×_
infixr 2 _⊎_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} →
  Set a →
  Set a
Not {a} proposition =
  proposition → Bottom {a}

_≠_ :
  {a : Level} →
  {A : Set a} →
  A →
  A →
  Set a
x ≠ y =
  Not (x ≡ y)

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor _,_
  field
    first  : A
    second : B

data _⊎_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → A ⊎ B
  right : B → A ⊎ B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤  : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ :
  Nat →
  Nat →
  Set
m < n =
  suc m ≤ n

record CommutativeRing
  {a : Level}
  (A : Set a) :
  Set a where

  field
    zeroR oneR : A
    addR multiplyR : A → A → A
    negateR : A → A

    add-associative :
      (x y z : A) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-commutative :
      (x y : A) →
      addR x y ≡ addR y x
    add-zero-left :
      (x : A) →
      addR zeroR x ≡ x
    add-zero-right :
      (x : A) →
      addR x zeroR ≡ x
    add-inverse-left :
      (x : A) →
      addR (negateR x) x ≡ zeroR
    add-inverse-right :
      (x : A) →
      addR x (negateR x) ≡ zeroR

    multiply-associative :
      (x y z : A) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-commutative :
      (x y : A) →
      multiplyR x y ≡ multiplyR y x
    multiply-one-left :
      (x : A) →
      multiplyR oneR x ≡ x
    multiply-one-right :
      (x : A) →
      multiplyR x oneR ≡ x
    distribute-left :
      (x y z : A) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : A) →
      multiplyR (addR x y) z ≡
      addR (multiplyR x z) (multiplyR y z)

difference :
  {a : Level} →
  {A : Set a} →
  CommutativeRing A →
  A →
  A →
  A
difference ring x y =
  CommutativeRing.addR ring x
    (CommutativeRing.negateR ring y)

Unit :
  {a : Level} →
  {A : Set a} →
  CommutativeRing A →
  A →
  Set a
Unit {A = A} ring x =
  Σ A
    (λ inverse →
      (CommutativeRing.multiplyR ring x inverse ≡
       CommutativeRing.oneR ring)
      ×
      (CommutativeRing.multiplyR ring inverse x ≡
       CommutativeRing.oneR ring))

record LocalRing
  {a : Level}
  {A : Set a}
  (ring : CommutativeRing A) :
  Set a where

  field
    nontrivial :
      CommutativeRing.oneR ring ≠
      CommutativeRing.zeroR ring
    unit-or-unit-of-sum-one :
      (x y : A) →
      CommutativeRing.addR ring x y ≡
      CommutativeRing.oneR ring →
      Unit ring x ⊎ Unit ring y

MaximalIdealMember :
  {a : Level} →
  {A : Set a} →
  {ring : CommutativeRing A} →
  LocalRing ring →
  A →
  Set a
MaximalIdealMember {ring = ring} local x =
  Not (Unit ring x)

data IdealPowerMember
  {a : Level}
  {A : Set a}
  (ring : CommutativeRing A)
  (ideal-member : A → Set a) :
  Nat →
  A →
  Set a where

  power-zero :
    {x : A} →
    IdealPowerMember ring ideal-member zero x

  power-suc-zero :
    {n : Nat} →
    IdealPowerMember ring ideal-member
      (suc n)
      (CommutativeRing.zeroR ring)

  power-suc-add :
    {n : Nat} →
    {x y : A} →
    IdealPowerMember ring ideal-member (suc n) x →
    IdealPowerMember ring ideal-member (suc n) y →
    IdealPowerMember ring ideal-member
      (suc n)
      (CommutativeRing.addR ring x y)

  power-suc-negate :
    {n : Nat} →
    {x : A} →
    IdealPowerMember ring ideal-member (suc n) x →
    IdealPowerMember ring ideal-member
      (suc n)
      (CommutativeRing.negateR ring x)

  power-suc-product :
    {n : Nat} →
    {x y : A} →
    IdealPowerMember ring ideal-member n x →
    ideal-member y →
    IdealPowerMember ring ideal-member
      (suc n)
      (CommutativeRing.multiplyR ring x y)

  power-respects-equality :
    {n : Nat} →
    {x y : A} →
    x ≡ y →
    IdealPowerMember ring ideal-member n x →
    IdealPowerMember ring ideal-member n y

record IsAdicComplete
  {a : Level}
  {A : Set a}
  (ring : CommutativeRing A)
  (ideal-member : A → Set a) :
  Set a where

  field
    separated :
      (x : A) →
      ((n : Nat) →
        IdealPowerMember ring ideal-member n x) →
      x ≡ CommutativeRing.zeroR ring

    precomplete :
      (sequence : Nat → A) →
      ((m n : Nat) →
        m ≤ n →
        IdealPowerMember ring ideal-member m
          (difference ring (sequence m) (sequence n))) →
      Σ A
        (λ limit →
          (n : Nat) →
          IdealPowerMember ring ideal-member n
            (difference ring (sequence n) limit))

PowerSeries :
  {a : Level} →
  Set a →
  Set a
PowerSeries A =
  Nat → A

oneSeries :
  {a : Level} →
  {A : Set a} →
  CommutativeRing A →
  PowerSeries A
oneSeries ring zero =
  CommutativeRing.oneR ring
oneSeries ring (suc n) =
  CommutativeRing.zeroR ring

multiplySeries :
  {a : Level} →
  {A : Set a} →
  CommutativeRing A →
  PowerSeries A →
  PowerSeries A →
  PowerSeries A
multiplySeries ring leftSeries rightSeries zero =
  CommutativeRing.multiplyR ring
    (leftSeries zero)
    (rightSeries zero)
multiplySeries ring leftSeries rightSeries (suc n) =
  CommutativeRing.addR ring
    (CommutativeRing.multiplyR ring
      (leftSeries zero)
      (rightSeries (suc n)))
    (multiplySeries ring
      (λ i → leftSeries (suc i))
      rightSeries
      n)

UnitSeries :
  {a : Level} →
  {A : Set a} →
  CommutativeRing A →
  PowerSeries A →
  Set a
UnitSeries {A = A} ring series =
  Σ (PowerSeries A)
    (λ inverse →
      ((n : Nat) →
        multiplySeries ring series inverse n ≡
        oneSeries ring n)
      ×
      ((n : Nat) →
        multiplySeries ring inverse series n ≡
        oneSeries ring n))

record Polynomial
  {a : Level}
  {A : Set a}
  (ring : CommutativeRing A) :
  Set a where

  field
    coefficient : Nat → A
    degree      : Nat
    zero-above-degree :
      (offset : Nat) →
      coefficient (degree + suc offset) ≡
      CommutativeRing.zeroR ring

Distinguished :
  {a : Level} →
  {A : Set a} →
  {ring : CommutativeRing A} →
  (local : LocalRing ring) →
  Polynomial ring →
  Set a
Distinguished {ring = ring} local polynomial =
  (Polynomial.coefficient polynomial
      (Polynomial.degree polynomial)
    ≡ CommutativeRing.oneR ring)
  ×
  ((n : Nat) →
    n < Polynomial.degree polynomial →
    MaximalIdealMember local
      (Polynomial.coefficient polynomial n))

ResidueImageNonzero :
  {a : Level} →
  {A : Set a} →
  {ring : CommutativeRing A} →
  LocalRing ring →
  PowerSeries A →
  Set a
ResidueImageNonzero local series =
  Not
    ((n : Nat) →
      MaximalIdealMember local (series n))

WeierstrassFactorization :
  {a : Level} →
  {A : Set a} →
  {ring : CommutativeRing A} →
  (local : LocalRing ring) →
  PowerSeries A →
  Polynomial ring →
  PowerSeries A →
  Set a
WeierstrassFactorization {ring = ring} local series polynomial unit-series =
  Distinguished local polynomial
  ×
  UnitSeries ring unit-series
  ×
  ((n : Nat) →
    series n ≡
    multiplySeries ring
      (Polynomial.coefficient polynomial)
      unit-series
      n)

-- Lean: PowerSeries.exists_isWeierstrassFactorization
weierstrass-preparation-theorem :
  (a : Level) →
  Set (lsuc a)
weierstrass-preparation-theorem a =
  {A : Set a} →
  (ring : CommutativeRing A) →
  (local : LocalRing ring) →
  IsAdicComplete ring (MaximalIdealMember local) →
  (series : PowerSeries A) →
  ResidueImageNonzero local series →
  Σ (Polynomial ring)
    (λ polynomial →
      Σ (PowerSeries A)
        (λ unit-series →
          WeierstrassFactorization
            local
            series
            polynomial
            unit-series))
