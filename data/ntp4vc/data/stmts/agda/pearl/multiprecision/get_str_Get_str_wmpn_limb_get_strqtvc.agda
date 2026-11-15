-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/get_str_Get_str_wmpn_limb_get_strqtvc: the verification
-- condition for converting one 64-bit limb into little-endian base digits,
-- preserving the represented value, digit bounds, pointer frame, and loop
-- progress invariants. This file contains no proof.

{-# OPTIONS --safe #-}

module get_str_Get_str_wmpn_limb_get_strqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_
infixr 2 _∨_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

absoluteNat : Int → Nat
absoluteNat (pos n) = n
absoluteNat (negsuc n) = suc n

powerNat : Int → Nat → Int
powerNat base zero = pos 1
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent = powerNat base (intToNat exponent)

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

natModulo : Nat → Nat → Nat
natModulo n zero = zero
natModulo n d@(suc _) = n - d * natDivide n d

computerDivide : Int → Int → Int
computerDivide _ (pos zero) = pos zero
computerDivide _ (negsuc _) = pos zero
computerDivide (pos n) (pos (suc m)) =
  pos (natDivide n (suc m))
computerDivide (negsuc n) (pos (suc m)) =
  negative (natDivide (suc n) (suc m))

euclideanModuloPositive : Int → Nat → Int
euclideanModuloPositive _ zero = pos zero
euclideanModuloPositive (pos n) d@(suc _) = pos (natModulo n d)
euclideanModuloPositive (negsuc n) d@(suc _) with natModulo (suc n) d
... | zero = pos zero
... | r@(suc _) = pos (d - r)

euclideanModulo : Int → Int → Int
euclideanModulo dividend divisor =
  euclideanModuloPositive dividend (absoluteNat divisor)

euclideanDivide : Int → Int → Int
euclideanDivide dividend divisor =
  computerDivide
    (subtractInt dividend (euclideanModulo dividend divisor))
    divisor

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

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

lowBit : Nat → Bool
lowBit zero = false
lowBit (suc zero) = true
lowBit (suc (suc n)) = lowBit n

natToVec : (width value : Nat) → Vec Bool width
natToVec zero value = []V
natToVec (suc width) value =
  lowBit value ∷V natToVec width (half value)

lastBit : {n : Nat} → Vec Bool (suc n) → Bool
lastBit {zero} (bit ∷V []V) = bit
lastBit {suc n} (_ ∷V bits) = lastBit bits

Word8 Word32 Word64 : Set
Word8 = Vec Bool 8
Word32 = Vec Bool 32
Word64 = Vec Bool 64

signed32 : Word32 → Int
signed32 bits with lastBit bits
... | false = unsignedZ bits
... | true = subtractInt (unsignedZ bits) (pos 4294967296)

zeroZ oneZ twoZ sevenZ sixtyThreeZ sixtyFourZ twoFiftyFiveZ
  twoFiftySixZ : Int
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2
sevenZ = pos 7
sixtyThreeZ = pos 63
sixtyFourZ = pos 64
twoFiftyFiveZ = pos 255
twoFiftySixZ = pos 256

max32Z max64Z radixZ : Int
max32Z = pos 2147483647
max64Z = pos 18446744073709551615
radixZ = pos 18446744073709551616

min32Z : Int
min32Z = negsuc 2147483647

int32InBounds : Int → Set
int32InBounds value =
  min32Z ≤Z value ∧ value ≤Z max32Z

uint64InBounds : Int → Set
uint64InBounds value =
  zeroZ ≤Z value ∧ value ≤Z max64Z

FunctionEqual :
  {A B : Set} → (A → B) → (A → B) → Set
FunctionEqual f g = (x : _) → f x ≡ g x

update :
  {A : Set} → (Int → A) → Int → A → Int → A
update f index value query with intEqual query index
... | true = value
... | false = f query

record Ptr (Zone A : Set) : Set where
  constructor pointer
  field
    memory    : Int → A
    cellCount : Nat
    off       : Int
    lo        : Int
    hi        : Int
    writeable : Bool
    region    : Zone

open Ptr public

pelts :
  {Zone A : Set} → Ptr Zone A → Int → A
pelts p = memory p

plength :
  {Zone A : Set} → Ptr Zone A → Int
plength p = pos (cellCount p)

valid :
  {Zone A : Set} → Ptr Zone A → Int → Set
valid p size =
  int32InBounds size
  ∧ zeroZ ≤Z size
  ∧ (zeroZ ≤Z lo p ∧ lo p ≤Z off p)
  ∧ addInt (off p) size ≤Z hi p
  ∧ hi p ≤Z plength p

accessAt :
  {Zone A : Set} → Ptr Zone A → Int → Set
accessAt p index =
  lo p ≤Z index ∧ index <Z hi p

sameFrame :
  {Zone A : Set} → Ptr Zone A → Ptr Zone A → Set
sameFrame newer older =
  cellCount newer ≡ cellCount older
  ∧ off newer ≡ off older
  ∧ lo newer ≡ lo older
  ∧ hi newer ≡ hi older
  ∧ writeable newer ≡ writeable older
  ∧ region newer ≡ region older

svalueLeMapFrom : Int → (Int → Word8) → Int → Nat → Int
svalueLeMapFrom base digits index zero = zeroZ
svalueLeMapFrom base digits index (suc count) =
  addInt
    (unsignedZ (digits index))
    (multiplyInt base
      (svalueLeMapFrom base digits (addInt index oneZ) count))

svalueLeSub : Int → (Int → Word8) → Int → Int → Int
svalueLeSub base digits lower upper =
  svalueLeMapFrom base digits lower
    (intToNat (subtractInt upper lower))

svalueLe :
  {Zone : Set} → Int → Ptr Zone Word8 → Int → Int
svalueLe base p size =
  svalueLeSub base (pelts p) (off p) (addInt (off p) size)

inBase :
  Int → (Int → Word8) → Int → Int → Set
inBase base digits lower upper =
  (index : Int) →
  (lower ≤Z index ∧ index <Z upper) →
  zeroZ ≤Z unsignedZ (digits index)
  ∧ unsignedZ (digits index) <Z base

outsideUnchanged :
  {Zone : Set} →
  Ptr Zone Word8 → Ptr Zone Word8 → Int → Set
outsideUnchanged current original end-index =
  (index : Int) →
  (index <Z off current
   ∨ addInt (off current) end-index ≤Z index) →
  pelts current index ≡ pelts original index

record BaseInfo : Set where
  constructor base-info
  field
    b             : Int
    exp           : Word32
    bb            : Word64
    baseLower     : twoZ ≤Z b
    baseUpper     : b ≤Z twoFiftySixZ
    blockBelow    : unsignedZ bb <Z radixZ
    nextAtLeast   : radixZ ≤Z multiplyInt (unsignedZ bb) b
    exponentLower : sevenZ ≤Z unsignedZ exp
    exponentUpper : unsignedZ exp ≤Z sixtyThreeZ
    blockPower    : unsignedZ bb ≡ powerInt b (unsignedZ exp)

open BaseInfo public

reciprocal : Word64 → Word64 → Set
reciprocal inverse divisor =
  unsignedZ inverse ≡
  subtractInt
    (euclideanDivide
      (subtractInt (multiplyInt radixZ radixZ) oneZ)
      (unsignedZ divisor))
    radixZ

InitialInvariant :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Word32 → Word64 → Set
InitialInvariant base sp size input =
  (zeroZ ≤Z unsignedZ input ∧ unsignedZ input <Z radixZ)
  ∧ (zeroZ ≤Z zeroZ ∧ zeroZ ≤Z signed32 size)
  ∧ (zeroZ <Z unsignedZ input →
      zeroZ ≤Z zeroZ ∧ zeroZ <Z signed32 size)
  ∧ inBase base (pelts sp) (off sp) (addInt (off sp) zeroZ)
  ∧ (unsignedZ input ≡ zeroZ →
      zeroZ <Z zeroZ →
      zeroZ <Z unsignedZ
        (pelts sp
          (subtractInt (addInt (off sp) zeroZ) oneZ)))
  ∧ unsignedZ input ≡
      addInt
        (svalueLe base sp zeroZ)
        (multiplyInt (powerInt base zeroZ) (unsignedZ input))

LoopInvariant :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Word32 → Word64 → Word32 → Word64 → Set
LoopInvariant base current-sp size input index remaining =
  (zeroZ ≤Z unsignedZ remaining ∧ unsignedZ remaining <Z radixZ)
  ∧ (zeroZ ≤Z signed32 index
     ∧ signed32 index ≤Z signed32 size)
  ∧ (zeroZ <Z unsignedZ remaining →
      zeroZ ≤Z signed32 index
      ∧ signed32 index <Z signed32 size)
  ∧ inBase base (pelts current-sp) (off current-sp)
      (addInt (off current-sp) (signed32 index))
  ∧ (unsignedZ remaining ≡ zeroZ →
      zeroZ <Z signed32 index →
      zeroZ <Z unsignedZ
        (pelts current-sp
          (subtractInt
            (addInt (off current-sp) (signed32 index))
            oneZ)))
  ∧ unsignedZ input ≡
      addInt
        (svalueLe base current-sp (signed32 index))
        (multiplyInt
          (powerInt base (signed32 index))
          (unsignedZ remaining))

DivisibleByShift : Word64 → Word64 → Set
DivisibleByShift remainder shift =
  (zeroZ ≤Z unsignedZ shift ∧ unsignedZ shift <Z sixtyFourZ)
  ∧ euclideanModulo
      (unsignedZ remainder)
      (powerInt twoZ (unsignedZ shift))
      ≡ zeroZ

AfterIncrement :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Word32 → Word64 →
  Ptr Zone Word8 → Word64 → Word64 → Word32 → Set
AfterIncrement base original-sp size input current-sp quotient remaining
  next-index =
  unsignedZ quotient <Z unsignedZ remaining
  ∧ (zeroZ ≤Z unsignedZ quotient
     ∧ unsignedZ quotient <Z radixZ)
  ∧ (zeroZ ≤Z signed32 next-index
     ∧ signed32 next-index ≤Z signed32 size)
  ∧ (zeroZ <Z unsignedZ quotient →
      zeroZ ≤Z signed32 next-index
      ∧ signed32 next-index <Z signed32 size)
  ∧ inBase base (pelts current-sp) (off current-sp)
      (addInt (off current-sp) (signed32 next-index))
  ∧ (unsignedZ quotient ≡ zeroZ →
      zeroZ <Z signed32 next-index →
      zeroZ <Z unsignedZ
        (pelts current-sp
          (subtractInt
            (addInt (off current-sp) (signed32 next-index))
            oneZ)))
  ∧ unsignedZ input ≡
      addInt
        (svalueLe base current-sp (signed32 next-index))
        (multiplyInt
          (powerInt base (signed32 next-index))
          (unsignedZ quotient))
  ∧ outsideUnchanged current-sp original-sp (signed32 next-index)

StoreContinuation :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Ptr Zone Word8 → Word32 → Word64 →
  Word64 → Word32 → Word64 → Word8 → Set
StoreContinuation {Zone} base original-sp current-sp size input remaining
  index quotient digit =
  ((accessAt current-sp (addInt (off current-sp) (signed32 index)))
   ∧ writeable current-sp ≡ true)
  ∧ ((stored : Ptr Zone Word8) →
      sameFrame stored current-sp →
      (FunctionEqual
        (pelts stored)
        (update
          (pelts current-sp)
          (addInt (off stored) (signed32 index))
          digit)
       ∧ pelts stored (addInt (off stored) (signed32 index)) ≡ digit) →
      int32InBounds (addInt (signed32 index) oneZ)
      ∧ ((next-index : Word32) →
          signed32 next-index ≡ addInt (signed32 index) oneZ →
          AfterIncrement base original-sp size input stored quotient
            remaining next-index))

DigitContinuation :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Ptr Zone Word8 → Word32 → Word64 →
  Word64 → Word32 → Word64 → Word64 → Set
DigitContinuation base original-sp current-sp size input remaining index
  quotient digit-value =
  (zeroZ ≤Z unsignedZ digit-value
   ∧ unsignedZ digit-value ≤Z twoFiftyFiveZ)
  ∧ ((digit : Word8) →
      unsignedZ digit ≡ unsignedZ digit-value →
      StoreContinuation base original-sp current-sp size input remaining
        index quotient digit)

NormalizedRemainder :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Ptr Zone Word8 → Word32 → Word64 →
  Word64 → Word32 → Word64 → Word64 → Word64 → Set
NormalizedRemainder base original-sp current-sp size input remaining index
  shift quotient remainder =
  DivisibleByShift remainder shift
  ∧ ((normalized : Word64) →
      unsignedZ remainder ≡
        multiplyInt
          (powerInt twoZ (unsignedZ shift))
          (unsignedZ normalized) →
      DivisibleByShift remainder shift
      ∧ ((digit-value : Word64) →
          unsignedZ remainder ≡
            multiplyInt
              (powerInt twoZ (unsignedZ shift))
              (unsignedZ digit-value) →
          DigitContinuation base original-sp current-sp size input
            remaining index quotient digit-value))

DivisionContinuation :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Ptr Zone Word8 → Word32 → Word64 →
  Word64 → Word32 → Word64 → Word64 → Word64 → Word64 → Word64 → Set
DivisionContinuation base original-sp current-sp size input remaining index
  shift divisor inverse high low =
  (euclideanDivide radixZ twoZ ≤Z unsignedZ divisor
   ∧ unsignedZ high <Z unsignedZ divisor
   ∧ reciprocal inverse divisor)
  ∧ ((quotient remainder : Word64) →
      addInt
        (multiplyInt (unsignedZ quotient) (unsignedZ divisor))
        (unsignedZ remainder)
        ≡ addInt
            (unsignedZ low)
            (multiplyInt radixZ (unsignedZ high))
      ∧ zeroZ ≤Z unsignedZ remainder
      ∧ unsignedZ remainder <Z unsignedZ divisor →
      NormalizedRemainder base original-sp current-sp size input remaining
        index shift quotient remainder)

LowContinuation :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Ptr Zone Word8 → Word32 → Word64 →
  Word64 → Word32 → Word64 → Word64 → Word64 → Word64 → Set
LowContinuation base original-sp current-sp size input remaining index shift
  divisor inverse high =
  (low : Word64) →
  unsignedZ low ≡
    euclideanModulo
      (multiplyInt
        (unsignedZ remaining)
        (powerInt twoZ (unsignedZ shift)))
      radixZ →
  DivisionContinuation base original-sp current-sp size input remaining
    index shift divisor inverse high low

HighContinuation :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Ptr Zone Word8 → Word32 → Word64 →
  Word64 → Word32 → Word64 → Word64 → Word64 → Word64 → Set
HighContinuation base original-sp current-sp size input remaining index shift
  divisor inverse offset =
  (high : Word64) →
  unsignedZ high ≡
    euclideanDivide
      (unsignedZ remaining)
      (powerInt twoZ (unsignedZ offset)) →
  (zeroZ ≤Z unsignedZ shift ∧ unsignedZ shift <Z sixtyFourZ)
  ∧ LowContinuation base original-sp current-sp size input remaining index
      shift divisor inverse high

OffsetContinuation :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Ptr Zone Word8 → Word32 → Word64 →
  Word64 → Word32 → Word64 → Word64 → Word64 → Set
OffsetContinuation base original-sp current-sp size input remaining index
  shift divisor inverse =
  (offset : Word64) →
  unsignedZ offset ≡ subtractInt sixtyFourZ (unsignedZ shift) →
  (zeroZ ≤Z unsignedZ offset ∧ unsignedZ offset <Z sixtyFourZ)
  ∧ HighContinuation base original-sp current-sp size input remaining index
      shift divisor inverse offset

PositiveBranch :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Ptr Zone Word8 → Word32 → Word64 →
  Word64 → Word32 → Word64 → Word64 → Word64 → Set
PositiveBranch base original-sp current-sp size input remaining index shift
  divisor inverse =
  uint64InBounds (subtractInt sixtyFourZ (unsignedZ shift))
  ∧ OffsetContinuation base original-sp current-sp size input remaining
      index shift divisor inverse

ZeroBranch :
  {Zone : Set} →
  BaseInfo → Ptr Zone Word8 → Word32 → Word64 →
  Word32 → Ptr Zone Word8 → Set
ZeroBranch info original-sp size input index current-sp =
  zeroZ ≤Z signed32 index
  ∧ ((result : Word32) →
      unsignedZ result ≡ signed32 index →
      svalueLe (b info) current-sp (unsignedZ result)
        ≡ unsignedZ input
      ∧ (zeroZ ≤Z unsignedZ result
         ∧ unsignedZ result ≤Z signed32 size)
      ∧ (zeroZ <Z unsignedZ result →
          zeroZ <Z unsignedZ
            (pelts current-sp
              (subtractInt
                (addInt (off current-sp) (unsignedZ result))
                oneZ)))
      ∧ outsideUnchanged current-sp original-sp (unsignedZ result)
      ∧ inBase (b info) (pelts current-sp) (off current-sp)
          (addInt (off current-sp) (unsignedZ result)))

Get-str-wmpn-limb-get-str-statement : Set₁
Get-str-wmpn-limb-get-str-statement =
  (Zone : Set) →
  (info : BaseInfo) →
  (sp : Ptr Zone Word8) →
  (divisor : Word64) →
  (shift : Word64) →
  (inverse : Word64) →
  (size : Word32) →
  (input : Word64) →
  twoZ ≤Z b info →
  b info ≤Z twoFiftySixZ →
  writeable sp ≡ true →
  euclideanDivide radixZ twoZ ≤Z unsignedZ divisor →
  zeroZ ≤Z unsignedZ shift →
  unsignedZ shift ≤Z sixtyThreeZ →
  multiplyInt (b info) (powerInt twoZ (unsignedZ shift))
    ≡ unsignedZ divisor →
  reciprocal inverse divisor →
  valid sp (signed32 size) →
  zeroZ <Z signed32 size →
  unsignedZ input <Z powerInt (b info) (signed32 size) →
  InitialInvariant (b info) sp size input
  ∧ ((index : Word32) →
      (remaining : Word64) →
      (current-sp : Ptr Zone Word8) →
      sameFrame current-sp sp →
      LoopInvariant (b info) current-sp size input index remaining →
      outsideUnchanged current-sp sp (signed32 index) →
      IfSet
        (intLess zeroZ (unsignedZ remaining))
        (PositiveBranch
          (b info) sp current-sp size input remaining index shift divisor
            inverse)
        (ZeroBranch info sp size input index current-sp))
