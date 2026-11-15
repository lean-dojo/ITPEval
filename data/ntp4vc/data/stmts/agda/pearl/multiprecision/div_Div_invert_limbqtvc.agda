-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/div_Div_invert_limbqtvc: the verification condition
-- establishing the bounds and reciprocal equation used to invert a
-- normalized unsigned 64-bit divisor. This file contains no proof.

{-# OPTIONS --safe #-}

module div_Div_invert_limbqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

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

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

data Vec (A : Set) : Nat → Set where
  []V   : Vec A zero
  _∷V_  : {n : Nat} → A → Vec A n → Vec A (suc n)

replicateVec : {A : Set} → (n : Nat) → A → Vec A n
replicateVec zero value = []V
replicateVec (suc n) value = value ∷V replicateVec n value

bitValue : Bool → Nat
bitValue false = zero
bitValue true = 1

unsignedNat : {n : Nat} → Vec Bool n → Nat
unsignedNat []V = zero
unsignedNat (bit ∷V bits) =
  bitValue bit + 2 * unsignedNat bits

unsignedZ : {n : Nat} → Vec Bool n → Int
unsignedZ bits = pos (unsignedNat bits)

Word64 : Set
Word64 = Vec Bool 64

maxWord : Word64
maxWord = replicateVec 64 true

zeroZ radixZ max64Z halfRadixZ : Int
zeroZ = pos 0
radixZ = pos 18446744073709551616
max64Z = pos 18446744073709551615
halfRadixZ = pos 9223372036854775808

radixNat reciprocalNumeratorNat : Nat
radixNat = 18446744073709551616
reciprocalNumeratorNat =
  radixNat * radixNat - 1

UInt64InBounds : Int → Set
UInt64InBounds value =
  zeroZ ≤Z value ∧ value ≤Z max64Z

reciprocal : Word64 → Word64 → Set
reciprocal v d =
  unsignedZ v ≡
  subtractInt
    (pos (natDivide reciprocalNumeratorNat (unsignedNat d)))
    radixZ

quotientNumerator : Word64 → Nat
quotientNumerator o2 =
  unsignedNat maxWord + radixNat * unsignedNat o2

invert-limb'vc : Set
invert-limb'vc =
  (d : Word64) →
  halfRadixZ ≤Z unsignedZ d →
  UInt64InBounds
    (subtractInt (unsignedZ maxWord) (unsignedZ d))
  ∧
  ((o2 : Word64) →
    unsignedZ o2 ≡
      subtractInt (unsignedZ maxWord) (unsignedZ d) →
    unsignedZ o2 <Z unsignedZ d
    ∧
    ((v : Word64) →
      unsignedZ v ≡
        pos (natDivide (quotientNumerator o2) (unsignedNat d)) →
      reciprocal v d))
