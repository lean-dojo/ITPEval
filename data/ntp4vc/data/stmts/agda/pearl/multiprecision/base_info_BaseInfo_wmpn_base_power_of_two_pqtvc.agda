-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/base_info_BaseInfo_wmpn_base_power_of_two_pqtvc:
-- the verification condition for recognizing powers of two from 2 through
-- 256 and returning their exponents as a 32-bit word. This file contains no proof.

{-# OPTIONS --safe #-}

module base_info_BaseInfo_wmpn_base_power_of_two_pqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_
infixr 5 _∷V_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

Word32 Word64 : Set
Word32 = Vec Bool 32
Word64 = Vec Bool 64

word32 : Nat → Word32
word32 = natToVec 32

word64 : Nat → Word64
word64 = natToVec 64

zeroZ twoZ eightZ twoHundredFiftySixZ : Int
zeroZ = pos 0
twoZ = pos 2
eightZ = pos 8
twoHundredFiftySixZ = pos 256

Recognition : Word64 → Bool → Nat → Set
Recognition b flag value =
  (unsignedZ b ≡ unsignedZ (word64 value) → flag ≡ true)
  ∧
  (flag ≡ true → b ≡ word64 value)

Stage8 : Word64 → Word32 → Set
Stage8 b result =
  Exists Bool
    (λ o8 →
      Recognition b o8 256
      ∧
      IfSet o8
        (result ≡ word32 8)
        (result ≡ word32 0))

Stage7 : Word64 → Word32 → Set
Stage7 b result =
  Exists Bool
    (λ o7 →
      Recognition b o7 128
      ∧
      IfSet o7
        (result ≡ word32 7)
        (Stage8 b result))

Stage6 : Word64 → Word32 → Set
Stage6 b result =
  Exists Bool
    (λ o6 →
      Recognition b o6 64
      ∧
      IfSet o6
        (result ≡ word32 6)
        (Stage7 b result))

Stage5 : Word64 → Word32 → Set
Stage5 b result =
  Exists Bool
    (λ o5 →
      Recognition b o5 32
      ∧
      IfSet o5
        (result ≡ word32 5)
        (Stage6 b result))

Stage4 : Word64 → Word32 → Set
Stage4 b result =
  Exists Bool
    (λ o4 →
      Recognition b o4 16
      ∧
      IfSet o4
        (result ≡ word32 4)
        (Stage5 b result))

Stage3 : Word64 → Word32 → Set
Stage3 b result =
  Exists Bool
    (λ o3 →
      Recognition b o3 8
      ∧
      IfSet o3
        (result ≡ word32 3)
        (Stage4 b result))

Stage2 : Word64 → Word32 → Set
Stage2 b result =
  Exists Bool
    (λ o2 →
      Recognition b o2 4
      ∧
      IfSet o2
        (result ≡ word32 2)
        (Stage3 b result))

InitialBranch : Word64 → Bool → Word32 → Set
InitialBranch b o1 result =
  IfSet o1
    (result ≡ word32 1)
    (Stage2 b result)

Conclusion : Word64 → Word32 → Set
Conclusion b result =
  zeroZ ≤Z unsignedZ result
  ∧
  unsignedZ result ≤Z eightZ
  ∧
  (unsignedZ result ≠ zeroZ →
    powerInt twoZ (unsignedZ result) ≡ unsignedZ b)
  ∧
  (unsignedZ result ≡ zeroZ →
    (n : Int) →
    zeroZ ≤Z n →
    powerInt twoZ n ≠ unsignedZ b)

wmpn-base-power-of-two-p'vc : Set
wmpn-base-power-of-two-p'vc =
  (b : Word64) →
  (o1 : Bool) →
  (result : Word32) →
  twoZ ≤Z unsignedZ b →
  unsignedZ b ≤Z twoHundredFiftySixZ →
  (unsignedZ b ≡ unsignedZ (word64 2) → o1 ≡ true) →
  (o1 ≡ true → b ≡ word64 2) →
  InitialBranch b o1 result →
  Conclusion b result
