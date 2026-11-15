-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/powm_Powm_binvert_limbqtvc: the verification condition
-- for Newton-style inversion of an odd unsigned 64-bit limb modulo powers of
-- two, including the lookup-table seed and three precision-doubling steps.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module powm_Powm_binvert_limbqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not A = A → Bottom

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
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

absoluteNat : Int → Nat
absoluteNat (pos n) = n
absoluteNat (negsuc n) = suc n

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

natModulo : Nat → Nat → Nat
natModulo n zero = zero
natModulo n d@(suc _) =
  n - d * natDivide n d

-- Signed quotient truncated toward zero, matching Why3's computer division.
tdivInt : Int → Int → Int
tdivInt (pos _) (pos zero) = pos zero
tdivInt (pos n) (pos (suc m)) = pos (natDivide n (suc m))
tdivInt (pos n) (negsuc m) = negative (natDivide n (suc m))
tdivInt (negsuc _) (pos zero) = pos zero
tdivInt (negsuc n) (pos (suc m)) =
  negative (natDivide (suc n) (suc m))
tdivInt (negsuc n) (negsuc m) =
  pos (natDivide (suc n) (suc m))

-- Signed remainder with the dividend's sign, matching Why3's computer modulo.
tmodInt : Int → Int → Int
tmodInt (pos n) divisor =
  pos (natModulo n (absoluteNat divisor))
tmodInt (negsuc n) divisor =
  negative (natModulo (suc n) (absoluteNat divisor))

-- Euclidean remainder for the positive moduli used by the VC.
euclideanModuloPositive : Int → Nat → Int
euclideanModuloPositive _ zero = pos zero
euclideanModuloPositive (pos n) d@(suc _) =
  pos (natModulo n d)
euclideanModuloPositive (negsuc n) d@(suc _) with natModulo (suc n) d
... | zero = pos zero
... | r@(suc _) = pos (d - r)

powerNat : Nat → Nat → Nat
powerNat base zero = 1
powerNat base (suc exponent) =
  base * powerNat base exponent

powerOfTwo : Int → Nat
powerOfTwo exponent = powerNat 2 (intToNat exponent)

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

Word64 : Set
Word64 = Vec Bool 64

zeroZ oneZ twoZ sixtyFourZ oneTwentyEightZ twoFiftySixZ : Int
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2
sixtyFourZ = pos 64
oneTwentyEightZ = pos 128
twoFiftySixZ = pos 256

radixNat max64Nat : Nat
radixNat = 18446744073709551616
max64Nat = 18446744073709551615

max64Z : Int
max64Z = pos max64Nat

UInt64InBounds : Int → Set
UInt64InBounds value =
  zeroZ ≤Z value ∧ value ≤Z max64Z

OddNat : Nat → Set
OddNat n =
  Exists Nat (λ k → n ≡ 2 * k + 1)

DoublePrecisionPremise : Int → Int → Int → Set
DoublePrecisionPremise n inv prec =
  (zeroZ ≤Z n ∧ zeroZ ≤Z inv)
  ∧
  euclideanModuloPositive
    (multiplyInt inv n)
    (powerOfTwo prec)
    ≡ oneZ
  ∧
  zeroZ ≤Z multiplyInt twoZ prec
  ∧
  multiplyInt twoZ prec ≤Z sixtyFourZ

DoublePrecisionConclusion : Int → Int → Int → Set
DoublePrecisionConclusion n inv prec =
  euclideanModuloPositive
    (multiplyInt
      (euclideanModuloPositive
        (subtractInt
          (multiplyInt twoZ inv)
          (multiplyInt inv (multiplyInt inv n)))
        radixNat)
      n)
    (powerOfTwo (multiplyInt twoZ prec))
  ≡ oneZ

DoublePrecisionObligation : Set
DoublePrecisionObligation =
  (n inv prec : Int) →
  DoublePrecisionPremise n inv prec →
  DoublePrecisionConclusion n inv prec

FinalCongruence : Word64 → Word64 → Set
FinalCongruence n o14 =
  euclideanModuloPositive
    (multiplyInt (unsignedZ o14) (unsignedZ n))
    radixNat
  ≡ oneZ

AfterO13 : Word64 → Word64 → Word64 → Set
AfterO13 n o12 o13 =
  (o14 : Word64) →
  unsignedZ o14 ≡
    euclideanModuloPositive
      (subtractInt (unsignedZ o13) (unsignedZ o12))
      radixNat →
  FinalCongruence n o14

AfterO12 : Word64 → Word64 → Word64 → Set
AfterO12 n o10 o12 =
  (o13 : Word64) →
  unsignedZ o13 ≡
    euclideanModuloPositive
      (multiplyInt twoZ (unsignedZ o10))
      radixNat →
  AfterO13 n o12 o13

AfterO11 : Word64 → Word64 → Word64 → Set
AfterO11 n o10 o11 =
  (o12 : Word64) →
  unsignedZ o12 ≡
    euclideanModuloPositive
      (multiplyInt (unsignedZ o10) (unsignedZ o11))
      radixNat →
  AfterO12 n o10 o12

AfterO10 : Word64 → Word64 → Set
AfterO10 n o10 =
  (o11 : Word64) →
  unsignedZ o11 ≡
    euclideanModuloPositive
      (multiplyInt (unsignedZ o10) (unsignedZ n))
      radixNat →
  AfterO11 n o10 o11

AfterO9 : Word64 → Word64 → Word64 → Set
AfterO9 n o8 o9 =
  (o10 : Word64) →
  unsignedZ o10 ≡
    euclideanModuloPositive
      (subtractInt (unsignedZ o9) (unsignedZ o8))
      radixNat →
  AfterO10 n o10

AfterO8 : Word64 → Word64 → Word64 → Set
AfterO8 n o6 o8 =
  (o9 : Word64) →
  unsignedZ o9 ≡
    euclideanModuloPositive
      (multiplyInt twoZ (unsignedZ o6))
      radixNat →
  AfterO9 n o8 o9

AfterO7 : Word64 → Word64 → Word64 → Set
AfterO7 n o6 o7 =
  (o8 : Word64) →
  unsignedZ o8 ≡
    euclideanModuloPositive
      (multiplyInt (unsignedZ o6) (unsignedZ o7))
      radixNat →
  AfterO8 n o6 o8

AfterO6 : Word64 → Word64 → Set
AfterO6 n o6 =
  (o7 : Word64) →
  unsignedZ o7 ≡
    euclideanModuloPositive
      (multiplyInt (unsignedZ o6) (unsignedZ n))
      radixNat →
  AfterO7 n o6 o7

AfterO5 : Word64 → Word64 → Word64 → Set
AfterO5 n o4 o5 =
  (o6 : Word64) →
  unsignedZ o6 ≡
    euclideanModuloPositive
      (subtractInt (unsignedZ o5) (unsignedZ o4))
      radixNat →
  AfterO6 n o6

AfterO4 : Word64 → Word64 → Word64 → Set
AfterO4 n o2 o4 =
  (o5 : Word64) →
  unsignedZ o5 ≡
    euclideanModuloPositive
      (multiplyInt twoZ (unsignedZ o2))
      radixNat →
  AfterO5 n o4 o5

AfterO3 : Word64 → Word64 → Word64 → Set
AfterO3 n o2 o3 =
  (o4 : Word64) →
  unsignedZ o4 ≡
    euclideanModuloPositive
      (multiplyInt (unsignedZ o2) (unsignedZ o3))
      radixNat →
  AfterO4 n o2 o4

AfterO2 : Word64 → Word64 → Set
AfterO2 n o2 =
  (o3 : Word64) →
  unsignedZ o3 ≡
    euclideanModuloPositive
      (multiplyInt (unsignedZ o2) (unsignedZ n))
      radixNat →
  AfterO3 n o2 o3

TablePremise : Word64 → Word64 → Set
TablePremise h o2 =
  (zeroZ ≤Z unsignedZ o2 ∧ unsignedZ o2 <Z twoFiftySixZ)
  ∧
  euclideanModuloPositive
    (multiplyInt
      (unsignedZ o2)
      (addInt (multiplyInt twoZ (unsignedZ h)) oneZ))
    (powerNat 2 8)
  ≡ oneZ

HObligation : Word64 → Word64 → Set
HObligation n o1 =
  (h : Word64) →
  unsignedZ h ≡ tmodInt (unsignedZ o1) oneTwentyEightZ →
  (zeroZ ≤Z unsignedZ h ∧ unsignedZ h <Z oneTwentyEightZ)
  ∧
  ((o2 : Word64) →
    TablePremise h o2 →
    AfterO2 n o2)

O1Obligation : Word64 → Set
O1Obligation n =
  (o1 : Word64) →
  unsignedZ o1 ≡ tdivInt (unsignedZ n) twoZ →
  (Not (oneTwentyEightZ ≡ zeroZ)
   ∧ UInt64InBounds (tmodInt (unsignedZ o1) oneTwentyEightZ))
  ∧
  HObligation n o1

binvert-limb'vc : Set
binvert-limb'vc =
  (n : Word64) →
  OddNat (unsignedNat n) →
  DoublePrecisionObligation
  ∧
  Not (twoZ ≡ zeroZ)
  ∧
  UInt64InBounds (tdivInt (unsignedZ n) twoZ)
  ∧
  O1Obligation n
