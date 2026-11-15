-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/incremental_Ce_int32_dummy_updateqtvc: a signed 32-bit dummy-update
-- verification condition whose second output is constrained by doubling the
-- first output. This file contains no proof.

{-# OPTIONS --safe #-}

module incremental_Ce_int32_dummy_updateqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_
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

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

data Vec (A : Set) : Nat → Set where
  []V  : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

bitValue : Bool → Nat
bitValue false = zero
bitValue true = suc zero

unsignedNat : {n : Nat} → Vec Bool n → Nat
unsignedNat []V = zero
unsignedNat (bit ∷V bits) =
  bitValue bit + (suc (suc zero)) * unsignedNat bits

lastBit : {n : Nat} → Vec Bool (suc n) → Bool
lastBit {zero} (bit ∷V []V) = bit
lastBit {suc n} (_ ∷V bits) = lastBit bits

Word32 : Set
Word32 = Vec Bool 32

signed : Word32 → Int
signed bits with lastBit bits
... | false = pos (unsignedNat bits)
... | true =
  subtractInt (pos (unsignedNat bits)) (pos 4294967296)

twentyTwo fortyTwo min32 max32 : Int
twentyTwo = pos 22
fortyTwo = pos 42
min32 = negsuc 2147483647
max32 = pos 2147483647

int32InBounds : Int → Set
int32InBounds x = min32 ≤Z x ∧ x ≤Z max32

dummy-update'vc : Set
dummy-update'vc =
  (r : Word32) →
  signed r ≡ twentyTwo →
  int32InBounds fortyTwo ∧
  ((o1 : Word32) →
   signed o1 ≡ fortyTwo →
   int32InBounds (addInt (signed o1) (signed o1)) ∧
   ((o2 : Word32) →
    signed o2 ≡ addInt (signed o1) (signed o1) →
    signed o2 ≡ fortyTwo))
