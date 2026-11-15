-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/airborne/float_rmat_inv/float_rmat_inv_Why3_ide_VCfloat_rmat_inv_post_goal0:
-- sequential memory updates copy a real 3-by-3 float matrix into a writable
-- destination in transposed order under the stated memory conditions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module float_rmat_inv_Why3_ide_VCfloat_rmat_inv_post_goal0 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤N_ _<N_ _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

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

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

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

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

andBool : Bool → Bool → Bool
andBool true b = b
andBool false _ = false

ifBool : {A : Set} → Bool → A → A → A
ifBool true yes _ = yes
ifBool false _ no = no

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
      lessOrEqualR x y ∨ lessOrEqualR y x
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
      lessOrEqualR zeroR oneR ∧ zeroR ≠ oneR

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

addrEqual : Addr → Addr → Bool
addrEqual (addr b i) (addr c j) =
  andBool (intEqual b c) (intEqual i j)

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

update : {A : Set} → (Addr → A) → Addr → A → Addr → A
update memory location value query =
  ifBool (addrEqual location query) value (memory query)

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

ValidRD : (Int → Int) → Addr → Int → Set
ValidRD allocation p n =
  zeroZ <Z n →
  (base p ≠ zeroZ) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

Separated : Addr → Int → Addr → Int → Set
Separated p a q b =
  (a ≤Z zeroZ) ∨
  (b ≤Z zeroZ) ∨
  (base p ≠ base q) ∨
  (addInt (offset q) b ≤Z offset p) ∨
  (addInt (offset p) a ≤Z offset q)

record RealRMat (R : Set) : Set where
  constructor realRMat
  field
    a00 a01 a02 : R
    a10 a11 a12 : R
    a20 a21 a22 : R

open RealRMat

MatrixEq : {R : Set} → RealRMat R → RealRMat R → Set
MatrixEq leftMatrix rightMatrix =
  a00 rightMatrix ≡ a00 leftMatrix ∧
  a01 rightMatrix ≡ a01 leftMatrix ∧
  a02 rightMatrix ≡ a02 leftMatrix ∧
  a10 rightMatrix ≡ a10 leftMatrix ∧
  a11 rightMatrix ≡ a11 leftMatrix ∧
  a12 rightMatrix ≡ a12 leftMatrix ∧
  a20 rightMatrix ≡ a20 leftMatrix ∧
  a21 rightMatrix ≡ a21 leftMatrix ∧
  a22 rightMatrix ≡ a22 leftMatrix

MatrixOfMemory : {R : Set} → (Addr → R) → Addr → RealRMat R
MatrixOfMemory memory matrix =
  let origin = shift matrix zeroZ
  in
  realRMat
    (memory (shift origin zeroZ))
    (memory (shift origin oneZ))
    (memory (shift origin twoZ))
    (memory (shift origin threeZ))
    (memory (shift origin fourZ))
    (memory (shift origin fiveZ))
    (memory (shift origin sixZ))
    (memory (shift origin sevenZ))
    (memory (shift origin eightZ))

Transpose : {R : Set} → RealRMat R → RealRMat R
Transpose matrix =
  realRMat
    (a00 matrix) (a10 matrix) (a20 matrix)
    (a01 matrix) (a11 matrix) (a21 matrix)
    (a02 matrix) (a12 matrix) (a22 matrix)

module VC
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set) where

  IsFinite32 : R → Set
  IsFinite32 _ = Top

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
    (memory : Addr → R) →
    (allocation : Int → Int) →
    let
      a2 = shift a zeroZ
      a3 = shift a1 zeroZ
      m =
        update memory
          (shift a2 zeroZ)
          (memory (shift a3 zeroZ))
      m1 =
        update m
          (shift a2 oneZ)
          (m (shift a3 threeZ))
      m2 =
        update m1
          (shift a2 twoZ)
          (m1 (shift a3 sixZ))
      m3 =
        update m2
          (shift a2 threeZ)
          (m2 (shift a3 oneZ))
      m4 =
        update m3
          (shift a2 fourZ)
          (m3 (shift a3 fourZ))
      m5 =
        update m4
          (shift a2 fiveZ)
          (m4 (shift a3 sevenZ))
      m6 =
        update m5
          (shift a2 sixZ)
          (m5 (shift a3 twoZ))
      m7 =
        update m6
          (shift a2 sevenZ)
          (m6 (shift a3 fiveZ))
      m8 =
        update m7
          (shift a2 eightZ)
          (m7 (shift a3 eightZ))
    in
    region (base a) ≤Z zeroZ →
    region (base a1) ≤Z zeroZ →
    linked allocation →
    ValidRW allocation a nineZ →
    RValidFloatRMat allocation memory a1 →
    Separated a nineZ a1 nineZ →
    MatrixEq
      (Transpose (MatrixOfMemory m8 a1))
      (MatrixOfMemory m8 a)

float-rmat-inv-post-goal0 : Set₂
float-rmat-inv-post-goal0 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  VC.goal0 {R} region linked
