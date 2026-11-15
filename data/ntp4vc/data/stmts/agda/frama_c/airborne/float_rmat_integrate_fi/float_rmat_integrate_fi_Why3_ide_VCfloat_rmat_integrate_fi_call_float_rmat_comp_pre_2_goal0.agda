-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/airborne/float_rmat_integrate_fi/float_rmat_integrate_fi_Why3_ide_VCfloat_rmat_integrate_fi_call_float_rmat_comp_pre_2_goal0:
-- a writable nine-entry float matrix destination is a readable valid float
-- matrix under the stated memory, allocation, and float-rate conditions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module FloatRMatIntegrateFiCallFloatRMatCompPreTwoGoal0 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤N_ _<N_ _≤Z_ _<Z_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not proposition = proposition → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record Top : Set where
  constructor truth

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _≤N_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤N n
  suc≤suc : {m n : Nat} → m ≤N n → suc m ≤N suc n

data _<N_ : Nat → Nat → Set where
  zero<suc : {n : Nat} → zero <N suc n
  suc<suc  : {m n : Nat} → m <N n → suc m <N suc n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = difference m (suc n)
addInt (negsuc m) (pos n) = difference n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

data _≤Z_ : Int → Int → Set where
  positive≤positive :
    {m n : Nat} →
    m ≤N n →
    pos m ≤Z pos n
  negative≤positive :
    {m n : Nat} →
    negsuc m ≤Z pos n
  negative≤negative :
    {m n : Nat} →
    n ≤N m →
    negsuc m ≤Z negsuc n

data _<Z_ : Int → Int → Set where
  positive<positive :
    {m n : Nat} →
    m <N n →
    pos m <Z pos n
  negative<positive :
    {m n : Nat} →
    negsuc m <Z pos n
  negative<negative :
    {m n : Nat} →
    n <N m →
    negsuc m <Z negsuc n

zeroZ oneZ twoZ threeZ fourZ fiveZ sixZ sevenZ eightZ nineZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))
fourZ = pos (suc (suc (suc (suc zero))))
fiveZ = pos (suc (suc (suc (suc (suc zero)))))
sixZ = pos (suc (suc (suc (suc (suc (suc zero))))))
sevenZ = pos (suc (suc (suc (suc (suc (suc (suc zero)))))))
eightZ = pos (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
nineZ = pos (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR reciprocalR : R → R
    lessOrEqualR : R → R → Set
    fromNatR : Nat → R

    one-not-zeroR :
      oneR ≠ zeroR

    add-commutativeR :
      (x y : R) → addR x y ≡ addR y x
    add-associativeR :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-zeroR :
      (x : R) → addR x zeroR ≡ x
    add-inverseR :
      (x : R) → addR x (negateR x) ≡ zeroR

    multiply-commutativeR :
      (x y : R) → multiplyR x y ≡ multiplyR y x
    multiply-associativeR :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) → multiplyR x oneR ≡ x
    multiply-zeroR :
      (x : R) → multiplyR x zeroR ≡ zeroR
    distributeR :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zeroR :
      reciprocalR zeroR ≡ zeroR
    multiply-reciprocalR :
      (x : R) →
      x ≠ zeroR →
      multiplyR x (reciprocalR x) ≡ oneR

    order-reflexiveR :
      (x : R) → lessOrEqualR x x
    order-transitiveR :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR y z →
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) →
      lessOrEqualR x y →
      lessOrEqualR y x →
      x ≡ y
    order-totalR :
      (x y : R) →
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-orderR :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) →
      lessOrEqualR zeroR x →
      lessOrEqualR zeroR y →
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      (lessOrEqualR zeroR oneR) ∧ (zeroR ≠ oneR)

    fromNat-zeroR :
      fromNatR zero ≡ zeroR
    fromNat-successorR :
      (n : Nat) →
      fromNatR (suc n) ≡ addR (fromNatR n) oneR
    fromNat-additionR :
      (m n : Nat) →
      fromNatR (m + n) ≡ addR (fromNatR m) (fromNatR n)
    fromNat-multiplicationR :
      (m n : Nat) →
      fromNatR (m * n) ≡ multiplyR (fromNatR m) (fromNatR n)
    fromNat-injectiveR :
      (m n : Nat) →
      fromNatR m ≡ fromNatR n →
      m ≡ n

    archimedeanR :
      (x : R) →
      Exists Nat (λ n → lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R → Set) →
      Exists R P →
      Exists R
        (λ upper →
          (x : R) →
          P x →
          lessOrEqualR x upper) →
      Exists R
        (λ supremum →
          ((x : R) →
            P x →
            lessOrEqualR x supremum)
          ∧
          ((upper : R) →
            ((x : R) →
              P x →
              lessOrEqualR x upper) →
            lessOrEqualR supremum upper))

open CompleteOrderedField

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) : Set₁ where
  field
    forwardR : R → S
    backwardR : S → R
    forward-after-backwardR :
      (y : S) → forwardR (backwardR y) ≡ y
    backward-after-forwardR :
      (x : R) → backwardR (forwardR x) ≡ x
    forward-zeroR :
      forwardR (zeroR source) ≡ zeroR target
    forward-oneR :
      forwardR (oneR source) ≡ oneR target
    forward-addR :
      (x y : R) →
      forwardR (addR source x y) ≡
      addR target (forwardR x) (forwardR y)
    forward-multiplyR :
      (x y : R) →
      forwardR (multiplyR source x y) ≡
      multiplyR target (forwardR x) (forwardR y)
    forward-negateR :
      (x : R) →
      forwardR (negateR source x) ≡ negateR target (forwardR x)
    forward-reciprocalR :
      (x : R) →
      forwardR (reciprocalR source x) ≡ reciprocalR target (forwardR x)
    forward-fromNatR :
      (n : Nat) →
      forwardR (fromNatR source n) ≡ fromNatR target n
    forward-orderR :
      (x y : R) →
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) : Set₂ where
  field
    equivalent-complete-ordered-field :
      (S : Set) →
      (other : CompleteOrderedField S) →
      CompleteOrderedFieldEquivalence reals other

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

ValidRD : (Int → Int) → Addr → Int → Set
ValidRD allocation p n =
  zeroZ <Z n →
  (zeroZ ≠ base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

module VC
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set) where

  IsFloat32 : R → Set
  IsFloat32 _ = Top

  IsFinite32 : R → Set
  IsFinite32 _ = Top

  FiniteFloatRates : (Addr → R) → Addr → Set
  FiniteFloatRates memory rates =
    IsFinite32 (memory (shift rates zeroZ)) ∧
    IsFinite32 (memory (shift rates oneZ)) ∧
    IsFinite32 (memory (shift rates twoZ))

  RValidFloatRates :
    (Int → Int) → (Addr → R) → Addr → Set
  RValidFloatRates allocation memory rates =
    FiniteFloatRates memory rates ∧
    ValidRD allocation rates threeZ

  FiniteFloatRMat : (Addr → R) → Addr → Set
  FiniteFloatRMat memory matrix =
    IsFinite32 (memory (shift matrix zeroZ)) ∧
    IsFinite32 (memory (shift matrix oneZ)) ∧
    IsFinite32 (memory (shift matrix twoZ)) ∧
    IsFinite32 (memory (shift matrix threeZ)) ∧
    IsFinite32 (memory (shift matrix fourZ)) ∧
    IsFinite32 (memory (shift matrix fiveZ)) ∧
    IsFinite32 (memory (shift matrix sixZ)) ∧
    IsFinite32 (memory (shift matrix sevenZ)) ∧
    IsFinite32 (memory (shift matrix eightZ))

  RValidFloatRMat :
    (Int → Int) → (Addr → R) → Addr → Set
  RValidFloatRMat allocation memory matrix =
    FiniteFloatRMat memory matrix ∧
    ValidRD allocation matrix nineZ

  goal0 : Set
  goal0 =
    (a a1 : Addr) →
    (allocation : Int → Int) →
    (memory : Addr → R) →
    region (base a) ≤Z zeroZ →
    region (base a1) ≤Z zeroZ →
    linked allocation →
    ValidRW allocation a nineZ →
    RValidFloatRates allocation memory a1 →
    IsFloat32 (memory (shift a1 zeroZ)) →
    IsFloat32 (memory (shift a1 oneZ)) →
    IsFloat32 (memory (shift a1 twoZ)) →
    RValidFloatRMat allocation memory a

float-rmat-integrate-fi-call-float-rmat-comp-pre-2-goal0 : Set₂
float-rmat-integrate-fi-call-float-rmat-comp-pre-2-goal0 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  VC.goal0 {R} region linked
