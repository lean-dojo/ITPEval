-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/powm_Powm_win_sizeqtvc: the signed 32-bit window-size
-- decision tree, its result bounds from zero through ten, and positivity for
-- positive inputs. This file contains no proof.

{-# OPTIONS --safe #-}

module powm_Powm_win_sizeqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

ifWord : {A : Set} → Bool → A → A → A
ifWord true when-true when-false = when-true
ifWord false when-true when-false = when-false

boolEqual : Bool → Bool → Bool
boolEqual false false = true
boolEqual false true = false
boolEqual true false = false
boolEqual true true = true

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

Word32 : Set
Word32 = Vec Bool 32

word : Nat → Word32
word = natToVec 32

zero32 one32 two32 three32 four32 five32 : Word32
six32 seven32 eight32 nine32 ten32 : Word32
zero32 = word 0
one32 = word 1
two32 = word 2
three32 = word 3
four32 = word 4
five32 = word 5
six32 = word 6
seven32 = word 7
eight32 = word 8
nine32 = word 9
ten32 = word 10

signed : Word32 → Int
signed bits with lastBit bits
... | false = pos (unsignedNat bits)
... | true =
  subtractInt (pos (unsignedNat bits)) (pos 4294967296)

windowChoice : Word32 → Bool → Word32
windowChoice eb o1 =
  ifWord (boolEqual o1 true) zero32
    (ifWord (intLessOrEqual (signed eb) (pos 7)) one32
      (ifWord (intLessOrEqual (signed eb) (pos 25)) two32
        (ifWord (intLessOrEqual (signed eb) (pos 81)) three32
          (ifWord (intLessOrEqual (signed eb) (pos 214)) four32
            (ifWord (intLessOrEqual (signed eb) (pos 673)) five32
              (ifWord (intLessOrEqual (signed eb) (pos 1793)) six32
                (ifWord (intLessOrEqual (signed eb) (pos 4609)) seven32
                  (ifWord (intLessOrEqual (signed eb) (pos 11521)) eight32
                    (ifWord
                      (intLessOrEqual (signed eb) (pos 28161))
                      nine32
                      ten32)))))))))

win-size'vc : Set
win-size'vc =
  (eb : Word32) →
  (o1 : Bool) →
  (result : Word32) →
  (signed eb ≡ signed zero32 → o1 ≡ true) →
  (o1 ≡ true → eb ≡ zero32) →
  result ≡ windowChoice eb o1 →
  (pos zero ≤Z signed result) ∧
  (signed result ≤Z pos 10) ∧
  (pos zero <Z signed eb → pos zero <Z signed result)
