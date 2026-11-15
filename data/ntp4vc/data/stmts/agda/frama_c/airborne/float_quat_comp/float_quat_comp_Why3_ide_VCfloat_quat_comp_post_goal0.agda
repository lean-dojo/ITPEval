-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/airborne/float_quat_comp/float_quat_comp_Why3_ide_VCfloat_quat_comp_post_goal0:
-- sequential memory updates computing a floating-point quaternion composition agree with
-- the corresponding real quaternion product under the stated separation and validity
-- conditions. This file contains no proof.

{-# OPTIONS --safe #-}

module float_quat_comp_Why3_ide_VCfloat_quat_comp_post_goal0 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_
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
  zero≤    : {n : Nat} → zero ≤N n
  suc≤suc  : {m n : Nat} → m ≤N n → suc m ≤N suc n

data _<N_ : Nat → Nat → Set where
  zero<suc : {n : Nat} → zero <N suc n
  suc<suc  : {m n : Nat} → m <N n → suc m <N suc n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

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

zeroZ oneZ twoZ threeZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))
fourZ = pos (suc (suc (suc (suc zero))))

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

record RealVect3 (R : Set) : Set where
  constructor vect3
  field
    x y z : R

record RealQuatVect (R : Set) : Set where
  constructor quat
  field
    scalar : R
    vect   : RealVect3 R

module VC
  {R : Set}
  (reals : CompleteOrderedField R)
  (region : Int → Int)
  (linked : (Int → Int) → Set) where

  open RealVect3
  open RealQuatVect

  infixl 6 _+R_
  infixl 7 _*R_

  _+R_ : R → R → R
  _+R_ = addR reals

  _*R_ : R → R → R
  _*R_ = multiplyR reals

  negR : R → R
  negR = negateR reals

  IsFinite32 : R → Set
  IsFinite32 _ = Top

  IsFloat32 : R → Set
  IsFloat32 _ = Top

  FiniteFloatQuat : (Addr → R) → Addr → Set
  FiniteFloatQuat memory q =
    IsFinite32 (memory (shift q zeroZ)) ∧
    IsFinite32 (memory (shift q oneZ)) ∧
    IsFinite32 (memory (shift q twoZ)) ∧
    IsFinite32 (memory (shift q threeZ))

  RValidFloatQuat : (Int → Int) → (Addr → R) → Addr → Set
  RValidFloatQuat allocation memory q =
    FiniteFloatQuat memory q ∧ ValidRD allocation q fourZ

  EqVect3 : RealVect3 R → RealVect3 R → Set
  EqVect3 leftVector rightVector =
    x rightVector ≡ x leftVector ∧
    y rightVector ≡ y leftVector ∧
    z rightVector ≡ z leftVector

  EqQuatVect : RealQuatVect R → RealQuatVect R → Set
  EqQuatVect leftQuat rightQuat =
    scalar rightQuat ≡ scalar leftQuat ∧
    EqVect3 (vect leftQuat) (vect rightQuat)

  scalarProduct : RealVect3 R → RealVect3 R → R
  scalarProduct leftVector rightVector =
    ((x leftVector *R x rightVector) +R
     (y leftVector *R y rightVector)) +R
    (z leftVector *R z rightVector)

  scaleVect : R → RealVect3 R → RealVect3 R
  scaleVect factor vector =
    vect3
      (factor *R x vector)
      (factor *R y vector)
      (factor *R z vector)

  addVect : RealVect3 R → RealVect3 R → RealVect3 R
  addVect leftVector rightVector =
    vect3
      (x leftVector +R x rightVector)
      (y leftVector +R y rightVector)
      (z leftVector +R z rightVector)

  crossProduct : RealVect3 R → RealVect3 R → RealVect3 R
  crossProduct leftVector rightVector =
    vect3
      (negR (z leftVector *R y rightVector) +R
       (y leftVector *R z rightVector))
      (negR (x leftVector *R z rightVector) +R
       (z leftVector *R x rightVector))
      (negR (y leftVector *R x rightVector) +R
       (x leftVector *R y rightVector))

  quatOfMemory : (Addr → R) → Addr → RealQuatVect R
  quatOfMemory memory q =
    quat
      (memory (shift q zeroZ))
      (vect3
        (memory (shift q oneZ))
        (memory (shift q twoZ))
        (memory (shift q threeZ)))

  multiplyQuat : RealQuatVect R → RealQuatVect R → RealQuatVect R
  multiplyQuat leftQuat rightQuat =
    let leftVector = vect leftQuat
        rightVector = vect rightQuat
        leftScalar = scalar leftQuat
        rightScalar = scalar rightQuat
    in
    quat
      (negR (scalarProduct leftVector rightVector) +R
       (leftScalar *R rightScalar))
      (addVect
        (addVect
          (scaleVect leftScalar rightVector)
          (scaleVect rightScalar leftVector))
        (crossProduct leftVector rightVector))

  goal0 : Set
  goal0 =
    (a1 a a2 : Addr) →
    (t1 : Addr → R) →
    (t : Int → Int) →
    let
      a3 = shift a1 zeroZ
      a4 = shift a zeroZ
      a5 = shift a2 zeroZ
      a6 = shift a oneZ
      a7 = shift a1 oneZ
      a8 = shift a2 oneZ
      a9 = shift a twoZ
      a10 = shift a1 twoZ
      a11 = shift a2 twoZ
      a12 = shift a threeZ
      a13 = shift a1 threeZ
      a14 = shift a2 threeZ
      r = t1 a4
      r1 = t1 a5
      r2 = t1 a6
      r3 = t1 a8
      r4 = t1 a9
      r5 = t1 a11
      r6 = t1 a12
      r7 = t1 a14
      m =
        update t1 a3
          ((((r1 *R r) +R negR (r3 *R r2)) +R
             negR (r5 *R r4)) +R
            negR (r7 *R r6))
      r8 = m a4
      r9 = m a5
      r10 = m a6
      r11 = m a8
      r12 = m a9
      r13 = m a11
      r14 = m a12
      r15 = m a14
      m1 =
        update m a7
          ((((r9 *R r10) +R (r11 *R r8)) +R
             (r13 *R r14)) +R
            negR (r15 *R r12))
      r16 = m1 a4
      r17 = m1 a5
      r18 = m1 a6
      r19 = m1 a8
      r20 = m1 a9
      r21 = m1 a11
      r22 = m1 a12
      r23 = m1 a14
      m2 =
        update m1 a10
          ((((r17 *R r20) +R negR (r19 *R r22)) +R
             (r21 *R r16)) +R
            (r23 *R r18))
      r24 = m2 a4
      r25 = m2 a5
      r26 = m2 a6
      r27 = m2 a8
      r28 = m2 a9
      r29 = m2 a11
      r30 = m2 a12
      r31 = m2 a14
      m3 =
        update m2 a13
          ((((r25 *R r30) +R (r27 *R r28)) +R
             negR (r29 *R r26)) +R
            (r31 *R r24))
    in
    a3 ≠ a4 →
    a5 ≠ a4 →
    a5 ≠ a3 →
    a6 ≠ a3 →
    a6 ≠ a5 →
    a7 ≠ a4 →
    a7 ≠ a5 →
    a7 ≠ a6 →
    a8 ≠ a4 →
    a8 ≠ a3 →
    a8 ≠ a6 →
    a8 ≠ a7 →
    a9 ≠ a3 →
    a9 ≠ a5 →
    a9 ≠ a7 →
    a9 ≠ a8 →
    a10 ≠ a4 →
    a10 ≠ a5 →
    a10 ≠ a6 →
    a10 ≠ a8 →
    a10 ≠ a9 →
    a11 ≠ a4 →
    a11 ≠ a3 →
    a11 ≠ a6 →
    a11 ≠ a7 →
    a11 ≠ a9 →
    a11 ≠ a10 →
    a12 ≠ a3 →
    a12 ≠ a5 →
    a12 ≠ a7 →
    a12 ≠ a8 →
    a12 ≠ a10 →
    a12 ≠ a11 →
    a13 ≠ a4 →
    a13 ≠ a5 →
    a13 ≠ a6 →
    a13 ≠ a8 →
    a13 ≠ a9 →
    a13 ≠ a11 →
    a13 ≠ a12 →
    a14 ≠ a4 →
    a14 ≠ a3 →
    a14 ≠ a6 →
    a14 ≠ a7 →
    a14 ≠ a9 →
    a14 ≠ a10 →
    a14 ≠ a12 →
    a14 ≠ a13 →
    region (base a) ≤Z zeroZ →
    region (base a1) ≤Z zeroZ →
    region (base a2) ≤Z zeroZ →
    linked t →
    ValidRW t a1 fourZ →
    RValidFloatQuat t t1 a →
    RValidFloatQuat t t1 a2 →
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
    IsFloat32 r18 →
    IsFloat32 r19 →
    IsFloat32 r20 →
    IsFloat32 r21 →
    IsFloat32 r22 →
    IsFloat32 r23 →
    IsFloat32 r24 →
    IsFloat32 r25 →
    IsFloat32 r26 →
    IsFloat32 r27 →
    IsFloat32 r28 →
    IsFloat32 r29 →
    IsFloat32 r30 →
    IsFloat32 r31 →
    EqQuatVect
      (quatOfMemory m3 a1)
      (multiplyQuat
        (quatOfMemory m3 a2)
        (quatOfMemory m3 a))

float-quat-comp-post-goal0 : Set₂
float-quat-comp-post-goal0 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  VC.goal0 reals region linked
