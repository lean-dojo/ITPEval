-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/airborne/float_rmat_vmult/float_rmat_vmult_Why3_ide_VCfloat_rmat_vmult_post_goal0:
-- three sequential memory updates compute multiplication of a real 3-by-3 matrix
-- by a real three-vector under the stated memory conditions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module float_rmat_vmult_Why3_ide_VCfloat_rmat_vmult_post_goal0 where

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

record RealVect3 (R : Set) : Set where
  constructor realVect3
  field
    x y z : R

open RealVect3

record RealRMat (R : Set) : Set where
  constructor realRMat
  field
    a00 a01 a02 : R
    a10 a11 a12 : R
    a20 a21 a22 : R

open RealRMat

VectorEq : {R : Set} → RealVect3 R → RealVect3 R → Set
VectorEq leftVector rightVector =
  x rightVector ≡ x leftVector ∧
  y rightVector ≡ y leftVector ∧
  z rightVector ≡ z leftVector

VectorOfMemory : {R : Set} → (Addr → R) → Addr → RealVect3 R
VectorOfMemory memory vector =
  realVect3
    (memory (shift vector zeroZ))
    (memory (shift vector oneZ))
    (memory (shift vector twoZ))

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

module VC
  {R : Set}
  (reals : CompleteOrderedField R)
  (region : Int → Int)
  (linked : (Int → Int) → Set) where

  infixl 6 _+R_
  infixl 7 _*R_

  _+R_ : R → R → R
  _+R_ = addR reals

  _*R_ : R → R → R
  _*R_ = multiplyR reals

  IsFinite32 : R → Set
  IsFinite32 _ = Top

  IsFloat32 : R → Set
  IsFloat32 _ = Top

  FiniteFloatVect3 : (Addr → R) → Addr → Set
  FiniteFloatVect3 memory vector =
    IsFinite32 (memory (shift vector zeroZ)) ∧
    IsFinite32 (memory (shift vector oneZ)) ∧
    IsFinite32 (memory (shift vector twoZ))

  RValidFloatVect3 :
    (Int → Int) → (Addr → R) → Addr → Set
  RValidFloatVect3 allocation memory vector =
    FiniteFloatVect3 memory vector ∧
    ValidRD allocation vector threeZ

  FiniteFloatRMat : (Addr → R) → Addr → Set
  FiniteFloatRMat memory matrix =
    let origin = shift matrix zeroZ
    in
    IsFinite32 (memory (shift origin zeroZ)) ∧
    IsFinite32 (memory (shift origin oneZ)) ∧
    IsFinite32 (memory (shift origin twoZ)) ∧
    IsFinite32 (memory (shift origin threeZ)) ∧
    IsFinite32 (memory (shift origin fourZ)) ∧
    IsFinite32 (memory (shift origin fiveZ)) ∧
    IsFinite32 (memory (shift origin sixZ)) ∧
    IsFinite32 (memory (shift origin sevenZ)) ∧
    IsFinite32 (memory (shift origin eightZ))

  RValidFloatRMat :
    (Int → Int) → (Addr → R) → Addr → Set
  RValidFloatRMat allocation memory matrix =
    FiniteFloatRMat memory matrix ∧
    ValidRD allocation matrix nineZ

  MultiplyMatrixVector : RealRMat R → RealVect3 R → RealVect3 R
  MultiplyMatrixVector matrix vector =
    realVect3
      (((a00 matrix *R x vector) +R (a01 matrix *R y vector)) +R
       (a02 matrix *R z vector))
      (((a10 matrix *R x vector) +R (a11 matrix *R y vector)) +R
       (a12 matrix *R z vector))
      (((a20 matrix *R x vector) +R (a21 matrix *R y vector)) +R
       (a22 matrix *R z vector))

  goal0 : Set
  goal0 =
    (a1 : Addr) →
    (t1 : Addr → R) →
    (a2 a : Addr) →
    (allocation : Int → Int) →
    let
      a3 = shift a1 zeroZ
      r = t1 a3
      a4 = shift a1 oneZ
      r1 = t1 a4
      a5 = shift a1 twoZ
      r2 = t1 a5
      a6 = shift a2 zeroZ
      r3 = t1 (shift a6 zeroZ)
      r4 = t1 (shift a6 oneZ)
      r5 = t1 (shift a6 twoZ)
      m =
        update t1 (shift a zeroZ)
          (((r3 *R r) +R (r4 *R r1)) +R (r5 *R r2))
      r6 = m a3
      r7 = m a4
      r8 = m a5
      r9 = m (shift a6 threeZ)
      r10 = m (shift a6 fourZ)
      r11 = m (shift a6 fiveZ)
      m1 =
        update m (shift a oneZ)
          (((r9 *R r6) +R (r10 *R r7)) +R (r11 *R r8))
      r12 = m1 a3
      r13 = m1 a4
      r14 = m1 a5
      r15 = m1 (shift a6 sixZ)
      r16 = m1 (shift a6 sevenZ)
      r17 = m1 (shift a6 eightZ)
      m2 =
        update m1 (shift a twoZ)
          (((r15 *R r12) +R (r16 *R r13)) +R (r17 *R r14))
    in
    region (base a) ≤Z zeroZ →
    region (base a1) ≤Z zeroZ →
    region (base a2) ≤Z zeroZ →
    linked allocation →
    ValidRW allocation a threeZ →
    RValidFloatVect3 allocation t1 a1 →
    RValidFloatRMat allocation t1 a2 →
    Separated a threeZ a1 threeZ →
    Separated a threeZ a2 nineZ →
    Separated a1 threeZ a2 nineZ →
    IsFloat32 r →
    IsFloat32 r1 →
    IsFloat32 r2 →
    IsFloat32 r3 →
    IsFloat32 r4 →
    IsFloat32 r5 →
    IsFloat32 r6 →
    IsFloat32 r7 →
    IsFloat32 r8 →
    IsFloat32 r9 →
    IsFloat32 r10 →
    IsFloat32 r11 →
    IsFloat32 r12 →
    IsFloat32 r13 →
    IsFloat32 r14 →
    IsFloat32 r15 →
    IsFloat32 r16 →
    IsFloat32 r17 →
    VectorEq
      (VectorOfMemory m2 a)
      (MultiplyMatrixVector
        (MatrixOfMemory m2 a2)
        (VectorOfMemory m2 a1))

float-rmat-vmult-post-goal0 : Set₂
float-rmat-vmult-post-goal0 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  VC.goal0 reals region linked
