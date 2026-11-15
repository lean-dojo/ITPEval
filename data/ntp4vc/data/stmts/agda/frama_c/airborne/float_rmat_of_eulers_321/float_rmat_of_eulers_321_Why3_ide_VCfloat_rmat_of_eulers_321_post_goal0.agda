-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/airborne/float_rmat_of_eulers_321/float_rmat_of_eulers_321_Why3_ide_VCfloat_rmat_of_eulers_321_post_goal0:
-- the 3-2-1 Euler-angle sine and cosine entries populate a writable real
-- 3-by-3 matrix whose rows are orthonormal under the stated memory and float conditions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module FloatRMatOfEulers321Why3IdeVCFloatRMatOfEulers321PostGoal0 where

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
    negateR reciprocalR absoluteValueR : R → R
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

    absolute-of-nonnegativeR :
      (x : R) →
      lessOrEqualR zeroR x →
      absoluteValueR x ≡ x
    absolute-of-nonpositiveR :
      (x : R) →
      lessOrEqualR x zeroR →
      absoluteValueR x ≡ negateR x

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
      forwardR (reciprocalR source x) ≡
      reciprocalR target (forwardR x)
    forward-absoluteR :
      (x : R) →
      forwardR (absoluteValueR source x) ≡
      absoluteValueR target (forwardR x)
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

subtract :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
subtract reals x y =
  addR reals x (negateR reals y)

divide :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
divide reals x y =
  multiplyR reals x (reciprocalR reals y)

StrictLess :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  Set
StrictLess reals x y =
  lessOrEqualR reals x y ∧ x ≠ y

SequentialLimit :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → R) →
  R →
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) →
  StrictLess reals (zeroR reals) epsilon →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤N n →
      StrictLess reals
        (absoluteValueR reals
          (subtract reals (sequence n) limit))
        epsilon)

power :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Nat →
  R
power reals x zero = oneR reals
power reals x (suc n) =
  multiplyR reals (power reals x n) x

factorial : Nat → Nat
factorial zero = suc zero
factorial (suc n) = suc n * factorial n

alternatingSign :
  {R : Set} →
  CompleteOrderedField R →
  Nat →
  R
alternatingSign reals zero = oneR reals
alternatingSign reals (suc n) =
  negateR reals (alternatingSign reals n)

evenIndex : Nat → Nat
evenIndex n = n + n

oddIndex : Nat → Nat
oddIndex n = suc (evenIndex n)

sumFirst :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → R) →
  Nat →
  R
sumFirst reals term zero = zeroR reals
sumFirst reals term (suc n) =
  addR reals (sumFirst reals term n) (term n)

cosinePartialSum :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Nat →
  R
cosinePartialSum reals x n =
  sumFirst reals
    (λ k →
      multiplyR reals
        (alternatingSign reals k)
        (divide reals
          (power reals x (evenIndex k))
          (fromNatR reals (factorial (evenIndex k)))))
    n

sinePartialSum :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Nat →
  R
sinePartialSum reals x n =
  sumFirst reals
    (λ k →
      multiplyR reals
        (alternatingSign reals k)
        (divide reals
          (power reals x (oddIndex k))
          (fromNatR reals (factorial (oddIndex k)))))
    n

record RealTrigonometry
  {R : Set}
  (reals : CompleteOrderedField R) : Set₁ where
  field
    sine cosine : R → R
    sine-series :
      (x : R) →
      SequentialLimit reals (sinePartialSum reals x) (sine x)
    cosine-series :
      (x : R) →
      SequentialLimit reals (cosinePartialSum reals x) (cosine x)

open RealTrigonometry

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

record RealRMat (R : Set) : Set where
  constructor realRMat
  field
    a00 a01 a02 : R
    a10 a11 a12 : R
    a20 a21 a22 : R

open RealRMat

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
  (trigonometry : RealTrigonometry reals)
  (region : Int → Int)
  (linked : (Int → Int) → Set) where

  infixl 6 _+R_
  infixl 7 _*R_

  _+R_ : R → R → R
  _+R_ = addR reals

  _*R_ : R → R → R
  _*R_ = multiplyR reals

  negR : R → R
  negR = negateR reals

  leR : R → R → Set
  leR = lessOrEqualR reals

  zeroReal oneReal : R
  zeroReal = zeroR reals
  oneReal = oneR reals

  IsFloat32 : R → Set
  IsFloat32 _ = Top

  IsFinite32 : R → Set
  IsFinite32 _ = Top

  FiniteFloatEulers : (Addr → R) → Addr → Set
  FiniteFloatEulers memory e =
    IsFinite32 (memory (shift e zeroZ)) ∧
    IsFinite32 (memory (shift e twoZ)) ∧
    IsFinite32 (memory (shift e oneZ))

  RValidFloatEulers :
    (Int → Int) → (Addr → R) → Addr → Set
  RValidFloatEulers allocation memory e =
    FiniteFloatEulers memory e ∧
    ValidRD allocation e threeZ

  MatrixEq : RealRMat R → RealRMat R → Set
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

  Transpose : RealRMat R → RealRMat R
  Transpose matrix =
    realRMat
      (a00 matrix) (a10 matrix) (a20 matrix)
      (a01 matrix) (a11 matrix) (a21 matrix)
      (a02 matrix) (a12 matrix) (a22 matrix)

  MatrixMultiply : RealRMat R → RealRMat R → RealRMat R
  MatrixMultiply leftMatrix rightMatrix =
    realRMat
      (((a00 leftMatrix *R a00 rightMatrix) +R
        (a01 leftMatrix *R a10 rightMatrix)) +R
        (a02 leftMatrix *R a20 rightMatrix))
      (((a00 leftMatrix *R a01 rightMatrix) +R
        (a01 leftMatrix *R a11 rightMatrix)) +R
        (a02 leftMatrix *R a21 rightMatrix))
      (((a00 leftMatrix *R a02 rightMatrix) +R
        (a01 leftMatrix *R a12 rightMatrix)) +R
        (a02 leftMatrix *R a22 rightMatrix))
      (((a10 leftMatrix *R a00 rightMatrix) +R
        (a11 leftMatrix *R a10 rightMatrix)) +R
        (a12 leftMatrix *R a20 rightMatrix))
      (((a10 leftMatrix *R a01 rightMatrix) +R
        (a11 leftMatrix *R a11 rightMatrix)) +R
        (a12 leftMatrix *R a21 rightMatrix))
      (((a10 leftMatrix *R a02 rightMatrix) +R
        (a11 leftMatrix *R a12 rightMatrix)) +R
        (a12 leftMatrix *R a22 rightMatrix))
      (((a20 leftMatrix *R a00 rightMatrix) +R
        (a21 leftMatrix *R a10 rightMatrix)) +R
        (a22 leftMatrix *R a20 rightMatrix))
      (((a20 leftMatrix *R a01 rightMatrix) +R
        (a21 leftMatrix *R a11 rightMatrix)) +R
        (a22 leftMatrix *R a21 rightMatrix))
      (((a20 leftMatrix *R a02 rightMatrix) +R
        (a21 leftMatrix *R a12 rightMatrix)) +R
        (a22 leftMatrix *R a22 rightMatrix))

  IdentityMatrix : RealRMat R
  IdentityMatrix =
    realRMat
      oneReal zeroReal zeroReal
      zeroReal oneReal zeroReal
      zeroReal zeroReal oneReal

  RotationMatrix : RealRMat R → Set
  RotationMatrix matrix =
    MatrixEq
      (MatrixMultiply matrix (Transpose matrix))
      IdentityMatrix

  goal0 : Set
  goal0 =
    (t1 : Addr → R) →
    (a1 a : Addr) →
    (allocation : Int → Int) →
    let
      r = t1 (shift a1 zeroZ)
      r1 = sine trigonometry r
      r2 = t1 (shift a1 twoZ)
      r3 = sine trigonometry r2
      r4 = t1 (shift a1 oneZ)
      r5 = sine trigonometry r4
      r6 = cosine trigonometry r
      r7 = cosine trigonometry r2
      r8 = cosine trigonometry r4
      a2 = shift a zeroZ
      r9 = r1 *R r5
      r10 = r6 *R r5
      memory0 =
        update t1
          (shift a2 zeroZ)
          (r8 *R r7)
      memory1 =
        update memory0
          (shift a2 oneZ)
          (r8 *R r3)
      memory2 =
        update memory1
          (shift a2 twoZ)
          (negR r5)
      memory3 =
        update memory2
          (shift a2 threeZ)
          ((r9 *R r7) +R negR (r6 *R r3))
      memory4 =
        update memory3
          (shift a2 fourZ)
          ((r9 *R r3) +R (r6 *R r7))
      memory5 =
        update memory4
          (shift a2 fiveZ)
          (r1 *R r8)
      memory6 =
        update memory5
          (shift a2 sixZ)
          ((r10 *R r7) +R (r1 *R r3))
      memory7 =
        update memory6
          (shift a2 sevenZ)
          ((r10 *R r3) +R negR (r1 *R r7))
      memory8 =
        update memory7
          (shift a2 eightZ)
          (r6 *R r8)
    in
    region (base a) ≤Z zeroZ →
    region (base a1) ≤Z zeroZ →
    leR r1 oneReal →
    leR r3 oneReal →
    leR r5 oneReal →
    leR r6 oneReal →
    leR r7 oneReal →
    leR r8 oneReal →
    leR (negR oneReal) r1 →
    leR (negR oneReal) r3 →
    leR (negR oneReal) r5 →
    leR (negR oneReal) r6 →
    leR (negR oneReal) r7 →
    leR (negR oneReal) r8 →
    linked allocation →
    ValidRW allocation a nineZ →
    RValidFloatEulers allocation t1 a1 →
    IsFinite32 r →
    IsFinite32 r2 →
    IsFinite32 r4 →
    IsFloat32 r →
    IsFloat32 r2 →
    IsFloat32 r4 →
    IsFinite32 r1 →
    IsFinite32 r3 →
    IsFinite32 r5 →
    IsFinite32 r6 →
    IsFinite32 r7 →
    IsFinite32 r8 →
    IsFloat32 r1 →
    IsFloat32 r3 →
    IsFloat32 r5 →
    IsFloat32 r6 →
    IsFloat32 r7 →
    IsFloat32 r8 →
    RotationMatrix (MatrixOfMemory memory8 a)

float-rmat-of-eulers-321-post-goal0 : Set₂
float-rmat-of-eulers-321-post-goal0 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (trigonometry : RealTrigonometry reals) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  VC.goal0 reals trigonometry region linked
