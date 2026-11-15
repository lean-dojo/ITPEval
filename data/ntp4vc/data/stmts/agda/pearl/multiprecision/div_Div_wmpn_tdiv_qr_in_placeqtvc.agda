-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/div_Div_wmpn_tdiv_qr_in_placeqtvc: the verification
-- condition for in-place multiprecision quotient-and-remainder division,
-- including allocation of temporary limb arrays and preservation of the
-- quotient/remainder specification. This file contains no proof.

{-# OPTIONS --safe #-}

module WmpnTdivQrInPlaceVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_
infixr 2 _↔_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

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

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

data Vec (A : Set) : Nat → Set where
  []V  : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

bitValue : Bool → Nat
bitValue false = zero
bitValue true = 1

unsignedNat : {n : Nat} → Vec Bool n → Nat
unsignedNat []V = zero
unsignedNat (bit ∷V bits) =
  bitValue bit + 2 * unsignedNat bits

unsignedZ : {n : Nat} → Vec Bool n → Int
unsignedZ bits = pos (unsignedNat bits)

lastBit : {n : Nat} → Vec Bool (suc n) → Bool
lastBit {zero} (bit ∷V []V) = bit
lastBit {suc n} (_ ∷V bits) = lastBit bits

Word32 Word64 : Set
Word32 = Vec Bool 32
Word64 = Vec Bool 64

signed32 : Word32 → Int
signed32 bits with lastBit bits
... | false = pos (unsignedNat bits)
... | true =
  subtractInt (pos (unsignedNat bits)) (pos 4294967296)

zero64 : Word64
zero64 =
  false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V
  false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V
  false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V
  false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V
  false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V
  false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V
  false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V
  false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V false ∷V
  []V

zeroZ oneZ : Int
zeroZ = pos 0
oneZ = pos 1

min32 max32 maxUnsigned32 radixZ : Int
min32 = negsuc 2147483647
max32 = pos 2147483647
maxUnsigned32 = pos 4294967295
radixZ = pos 18446744073709551616

int32InBounds : Int → Set
int32InBounds n = min32 ≤Z n ∧ n ≤Z max32

uint32InBounds : Int → Set
uint32InBounds n = zeroZ ≤Z n ∧ n ≤Z maxUnsigned32

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ _) = x
nthDefault default (suc _) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

record Ptr (Zone A : Set) : Set where
  constructor pointer
  field
    ptrData   : List A
    off       : Int
    lo        : Int
    hi        : Int
    writeable : Bool
    region    : Zone

open Ptr public

pelts : {Zone : Set} → Ptr Zone Word64 → Int → Word64
pelts p index =
  nthDefault zero64 (intToNat index) (ptrData p)

plength : {Zone : Set} → Ptr Zone Word64 → Int
plength p = pos (length (ptrData p))

valid : {Zone : Set} → Ptr Zone Word64 → Int → Set
valid p size =
  int32InBounds size
  ∧ zeroZ ≤Z size
  ∧ (zeroZ ≤Z lo p ∧ lo p ≤Z off p)
  ∧ addInt (off p) size ≤Z hi p
  ∧ hi p ≤Z plength p

sameShape :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
sameShape newer older =
  length (ptrData newer) ≡ length (ptrData older)
  ∧ off newer ≡ off older
  ∧ lo newer ≡ lo older
  ∧ hi newer ≡ hi older
  ∧ writeable newer ≡ writeable older
  ∧ region newer ≡ region older

valueFrom :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Nat →
  Int
valueFrom p index zero = zeroZ
valueFrom p index (suc count) =
  addInt
    (unsignedZ (pelts p index))
    (multiplyInt
      radixZ
      (valueFrom p (addInt index oneZ) count))

value :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Int
value p size =
  valueFrom p (off p) (intToNat size)

isNotNull :
  {Zone : Set} →
  Ptr Zone Word64 →
  Zone →
  Set
isNotNull p nullZone =
  Not (region p ≡ nullZone)

isNotNullSpec :
  {Zone : Set} →
  Ptr Zone Word64 →
  Zone →
  Set
isNotNullSpec p nullZone =
  isNotNull p nullZone ↔ Not (region p ≡ nullZone)

allocationPost :
  {Zone : Set} →
  Ptr Zone Word64 →
  Zone →
  Int →
  Set
allocationPost p nullZone requestedLength =
  (Not (region p ≡ nullZone) →
    plength p ≡ requestedLength)
  ∧ off p ≡ zeroZ
  ∧ lo p ≡ zeroZ
  ∧ hi p ≡ plength p
  ∧ writeable p ≡ true

canonicalFrame :
  {Zone : Set} →
  Ptr Zone Word64 →
  Set
canonicalFrame p =
  off p ≡ zeroZ
  ∧ lo p ≡ zeroZ
  ∧ hi p ≡ plength p
  ∧ writeable p ≡ true

divisionResult :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Set
divisionResult originalX quotient divisor remainder sx sy =
  value originalX (signed32 sx)
    ≡ addInt
        (multiplyInt
          (value quotient
            (addInt
              (subtractInt (signed32 sx) (signed32 sy))
              oneZ))
          (value divisor (signed32 sy)))
        (value remainder (signed32 sy))
  ∧ value remainder (signed32 sy)
      <Z value divisor (signed32 sy)

finalContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Set
finalContinuation x y q nx ny sx sy =
  (ny₁ nx₁ x₁ q₁ : Ptr _ Word64) →
  sameShape ny₁ ny →
  sameShape nx₁ nx →
  sameShape x₁ x →
  sameShape q₁ q →
  divisionResult x q₁ y x₁ sx sy →
  canonicalFrame nx₁
  ∧ canonicalFrame ny₁
  ∧ divisionResult x q₁ y x₁ sx sy

innerObligation :
  {Zone : Set} →
  Zone →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
innerObligation nullZone sy sx x y q nx ny =
  ((oneZ ≤Z signed32 sy
    ∧ signed32 sy ≤Z signed32 sx
    ∧ signed32 sx ≤Z subtractInt max32 oneZ)
   ∧ valid x (signed32 sx)
   ∧ valid y (signed32 sy)
   ∧ valid q
       (addInt
         (subtractInt (signed32 sx) (signed32 sy))
         oneZ)
   ∧ valid nx (addInt (signed32 sx) oneZ)
   ∧ valid ny (signed32 sy)
   ∧ (writeable q ≡ true ∧ writeable x ≡ true)
   ∧ (writeable nx ≡ true ∧ writeable ny ≡ true)
   ∧ zeroZ <Z
       unsignedZ
         (pelts y
           (subtractInt
             (addInt (off y) (signed32 sy))
             oneZ)))
  ∧ finalContinuation x y q nx ny sx sy

secondAllocation :
  {Zone : Set} →
  Zone →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
secondAllocation nullZone sy sx x y q nx =
  zeroZ ≤Z signed32 sy
  ∧
  ((o₃ : Word32) →
    unsignedZ o₃ ≡ signed32 sy →
    zeroZ ≤Z unsignedZ o₃
    ∧
    ((ny : Ptr _ Word64) →
      allocationPost ny nullZone (unsignedZ o₃) →
      isNotNullSpec ny nullZone →
      isNotNull ny nullZone →
      innerObligation nullZone sy sx x y q nx ny))

firstAllocation :
  {Zone : Set} →
  Zone →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
firstAllocation nullZone sy sx x y q =
  (o₁ : Word32) →
  unsignedZ o₁ ≡ signed32 sx →
  uint32InBounds (addInt (unsignedZ o₁) oneZ)
  ∧
  ((o₂ : Word32) →
    unsignedZ o₂ ≡ addInt (unsignedZ o₁) oneZ →
    zeroZ ≤Z unsignedZ o₂
    ∧
    ((nx : Ptr _ Word64) →
      allocationPost nx nullZone (unsignedZ o₂) →
      isNotNullSpec nx nullZone →
      isNotNull nx nullZone →
      secondAllocation nullZone sy sx x y q nx))

wmpn-tdiv-qr-in-place'vc : Set₁
wmpn-tdiv-qr-in-place'vc =
  (Zone : Set) →
  (nullZone : Zone) →
  (sy sx : Word32) →
  (x y q : Ptr Zone Word64) →
  (qxn : Word32) →
  oneZ ≤Z signed32 sy →
  signed32 sy ≤Z signed32 sx →
  signed32 sx ≤Z subtractInt max32 oneZ →
  valid x (signed32 sx) →
  valid y (signed32 sy) →
  valid q
    (addInt
      (subtractInt (signed32 sx) (signed32 sy))
      oneZ) →
  writeable x ≡ true →
  writeable q ≡ true →
  signed32 qxn ≡ zeroZ →
  zeroZ <Z
    unsignedZ
      (pelts y
        (subtractInt
          (addInt (off y) (signed32 sy))
          oneZ)) →
  zeroZ ≤Z signed32 sx
  ∧ firstAllocation nullZone sy sx x y q
