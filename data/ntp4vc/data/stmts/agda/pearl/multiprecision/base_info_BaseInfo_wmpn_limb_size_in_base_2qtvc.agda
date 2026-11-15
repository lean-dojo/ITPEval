-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/base_info_BaseInfo_wmpn_limb_size_in_base_2qtvc:
-- the verification condition that a positive 64-bit limb lies between the
-- consecutive powers of two determined by its leading-zero count, including
-- the fixed-width conversion and range side conditions. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module BaseInfoWmpnLimbSizeInBaseTwoVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

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
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

powerNat : Int → Nat → Int
powerNat base zero = pos 1
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent = powerNat base (intToNat exponent)

data Vec (A : Set) : Nat → Set where
  []V   : Vec A zero
  _∷V_  : {n : Nat} → A → Vec A n → Vec A (suc n)

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

zeroZ oneZ twoZ sixtyFourZ max64Z : Int
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2
sixtyFourZ = pos 64
max64Z = pos 18446744073709551615

UInt64InBounds : Int → Set
UInt64InBounds value =
  zeroZ ≤Z value ∧ value ≤Z max64Z

ResultObligation : Word64 → Word64 → Set
ResultObligation u shift =
  (r : Word64) →
  unsignedZ r ≡ subtractInt sixtyFourZ (unsignedZ shift) →
  (oneZ ≤Z unsignedZ r ∧ unsignedZ r ≤Z sixtyFourZ)
  ∧
  powerInt twoZ (subtractInt (unsignedZ r) oneZ) ≤Z unsignedZ u
  ∧
  unsignedZ u <Z powerInt twoZ (unsignedZ r)

ShiftObligation : Word64 → Int → Set
ShiftObligation u signed-count =
  (shift : Word64) →
  unsignedZ shift ≡ signed-count →
  UInt64InBounds (subtractInt sixtyFourZ (unsignedZ shift))
  ∧
  ResultObligation u shift

LeadingZeroPremise : Word64 → Word32 → Set
LeadingZeroPremise u o1 =
  multiplyInt
    (powerInt twoZ (signed32 o1))
    (unsignedZ u)
    ≤Z max64Z
  ∧
  max64Z
    <Z multiplyInt
          (multiplyInt twoZ (powerInt twoZ (signed32 o1)))
          (unsignedZ u)
  ∧
  zeroZ ≤Z signed32 o1
  ∧
  signed32 o1 <Z sixtyFourZ

LeadingZeroObligation : Word64 → Set
LeadingZeroObligation u =
  (o1 : Word32) →
  LeadingZeroPremise u o1 →
  zeroZ ≤Z signed32 o1
  ∧
  ShiftObligation u (signed32 o1)

wmpn-limb-size-in-base-2'vc : Set
wmpn-limb-size-in-base-2'vc =
  (u : Word64) →
  zeroZ <Z unsignedZ u →
  zeroZ <Z unsignedZ u
  ∧
  LeadingZeroObligation u
