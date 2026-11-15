-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/div_Div_reciprocal_word_3by2qtvc: the verification
-- condition for computing a reciprocal approximation to a normalized
-- two-limb 64-bit divisor, including its correction branches. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module div_Div_reciprocal_word_3by2qtvc where

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfBool : Bool → Bool → Bool → Bool
IfBool true when-true when-false = when-true
IfBool false when-true when-false = when-false

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

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

natModulo : Nat → Nat → Nat
natModulo n zero = zero
natModulo n d@(suc _) =
  n - d * natDivide n d

euclideanModuloPositive : Int → Nat → Int
euclideanModuloPositive _ zero = pos zero
euclideanModuloPositive (pos n) d@(suc _) =
  pos (natModulo n d)
euclideanModuloPositive (negsuc n) d@(suc _) with natModulo (suc n) d
... | zero = pos zero
... | r@(suc _) = pos (d - r)

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

zeroZ oneZ radixZ max64Z halfRadixZ : Int
zeroZ = pos 0
oneZ = pos 1
radixZ = pos 18446744073709551616
max64Z = pos 18446744073709551615
halfRadixZ = pos 9223372036854775808

radixNat reciprocalNumeratorNat reciprocal3NumeratorNat : Nat
radixNat = 18446744073709551616
reciprocalNumeratorNat =
  radixNat * radixNat - 1
reciprocal3NumeratorNat =
  radixNat * radixNat * radixNat - 1

UInt64InBounds : Int → Set
UInt64InBounds value =
  zeroZ ≤Z value ∧ value ≤Z max64Z

reciprocal : Word64 → Word64 → Set
reciprocal v d =
  unsignedZ v ≡
  subtractInt
    (pos (natDivide reciprocalNumeratorNat (unsignedNat d)))
    radixZ

divisorNat : Word64 → Word64 → Nat
divisorNat dh dl =
  unsignedNat dl + radixNat * unsignedNat dh

reciprocal3by2 : Word64 → Word64 → Word64 → Set
reciprocal3by2 v dh dl =
  unsignedZ v ≡
  subtractInt
    (pos (natDivide reciprocal3NumeratorNat (divisorNat dh dl)))
    radixZ

FlagPremise :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Bool →
  Set
FlagPremise dh dl high productLow decision =
  IfSet
    (intLess (unsignedZ dh) (unsignedZ high))
    (decision ≡ true)
    (Exists
      Bool
      (λ equalFlag →
        ((unsignedZ high ≡ unsignedZ dh → equalFlag ≡ true)
         ∧ (equalFlag ≡ true → high ≡ dh))
        ∧ decision ≡
          IfBool
            equalFlag
            (IfBool
              (intLessOrEqual
                (unsignedZ dl)
                (unsignedZ productLow))
              true
              false)
            false))

DecisionResult :
  Word64 →
  Word64 →
  Word64 →
  Bool →
  Set
DecisionResult quotient dh dl decision =
  IfSet
    decision
    (UInt64InBounds (subtractInt (unsignedZ quotient) oneZ)
     ∧
     ((decremented : Word64) →
       unsignedZ decremented ≡
         subtractInt (unsignedZ quotient) oneZ →
       UInt64InBounds
         (subtractInt (unsignedZ decremented) oneZ)
       ∧
       ((twiceDecremented : Word64) →
         unsignedZ twiceDecremented ≡
           subtractInt (unsignedZ decremented) oneZ →
         reciprocal3by2 twiceDecremented dh dl)))
    (UInt64InBounds (subtractInt (unsignedZ quotient) oneZ)
     ∧
     ((decremented : Word64) →
       unsignedZ decremented ≡
         subtractInt (unsignedZ quotient) oneZ →
       reciprocal3by2 decremented dh dl))

CarryCorrection :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
CarryCorrection quotient dh dl productLow productHigh high =
  IfSet
    (intLess (unsignedZ high) (unsignedZ productHigh))
    ((decision : Bool) →
      FlagPremise dh dl high productLow decision →
      DecisionResult quotient dh dl decision)
    (reciprocal3by2 quotient dh dl)

AfterDeepHighSum :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
AfterDeepHighSum quotient dh dl productLow productHigh reduced high =
  unsignedZ high ≡
    euclideanModuloPositive
      (addInt (unsignedZ reduced) (unsignedZ productHigh))
      radixNat →
  CarryCorrection quotient dh dl productLow productHigh high

DeepProduct :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
DeepProduct quotient dh dl decrementedRemainder =
  (productLow productHigh : Word64) →
  addInt
    (unsignedZ productLow)
    (multiplyInt radixZ (unsignedZ productHigh))
  ≡
  multiplyInt (unsignedZ quotient) (unsignedZ dl) →
  ((high : Word64) →
    AfterDeepHighSum
      quotient dh dl productLow productHigh
      decrementedRemainder high)

DeepRemainder :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
DeepRemainder quotient dh dl remainder =
  (decrementedRemainder : Word64) →
  unsignedZ decrementedRemainder ≡
    euclideanModuloPositive
      (subtractInt (unsignedZ remainder) (unsignedZ dh))
      radixNat →
  DeepProduct quotient dh dl decrementedRemainder

HighCarryBranch :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
HighCarryBranch original dh dl remainderAfterCarry =
  UInt64InBounds (subtractInt (unsignedZ original) oneZ)
  ∧
  ((decremented : Word64) →
    unsignedZ decremented ≡
      subtractInt (unsignedZ original) oneZ →
    UInt64InBounds
      (subtractInt
        (unsignedZ remainderAfterCarry)
        (unsignedZ dh))
    ∧
    ((remainder : Word64) →
      unsignedZ remainder ≡
        subtractInt
          (unsignedZ remainderAfterCarry)
          (unsignedZ dh) →
      UInt64InBounds
        (subtractInt (unsignedZ decremented) oneZ)
      ∧
      ((twiceDecremented : Word64) →
        unsignedZ twiceDecremented ≡
          subtractInt (unsignedZ decremented) oneZ →
        DeepRemainder
          twiceDecremented dh dl remainder)))

LowCarryProduct :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
LowCarryProduct quotient dh dl reduced =
  (productLow productHigh : Word64) →
  addInt
    (unsignedZ productLow)
    (multiplyInt radixZ (unsignedZ productHigh))
  ≡
  multiplyInt (unsignedZ quotient) (unsignedZ dl) →
  ((high : Word64) →
    unsignedZ high ≡
      euclideanModuloPositive
        (addInt (unsignedZ reduced) (unsignedZ productHigh))
        radixNat →
    CarryCorrection quotient dh dl productLow productHigh high)

LowCarryBranch :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
LowCarryBranch original dh dl remainderAfterCarry =
  UInt64InBounds (subtractInt (unsignedZ original) oneZ)
  ∧
  ((decremented : Word64) →
    unsignedZ decremented ≡
      subtractInt (unsignedZ original) oneZ →
    (reduced : Word64) →
    unsignedZ reduced ≡
      euclideanModuloPositive
        (subtractInt
          (unsignedZ remainderAfterCarry)
          (unsignedZ dh))
        radixNat →
    LowCarryProduct decremented dh dl reduced)

NoCarryProduct :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
NoCarryProduct quotient dh dl remainder =
  (productLow productHigh : Word64) →
  addInt
    (unsignedZ productLow)
    (multiplyInt radixZ (unsignedZ productHigh))
  ≡
  multiplyInt (unsignedZ quotient) (unsignedZ dl) →
  ((high : Word64) →
    unsignedZ high ≡
      euclideanModuloPositive
        (addInt (unsignedZ remainder) (unsignedZ productHigh))
        radixNat →
    CarryCorrection quotient dh dl productLow productHigh high)

AfterRemainder :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
AfterRemainder quotient dh dl remainder =
  IfSet
    (intLess (unsignedZ remainder) (unsignedZ dl))
    (IfSet
      (intLessOrEqual (unsignedZ dh) (unsignedZ remainder))
      (HighCarryBranch quotient dh dl remainder)
      (LowCarryBranch quotient dh dl remainder))
    (NoCarryProduct quotient dh dl remainder)

AfterLowProduct :
  Word64 →
  Word64 →
  Word64 →
  Set
AfterLowProduct quotient dh dl =
  (lowProduct : Word64) →
  unsignedZ lowProduct ≡
    euclideanModuloPositive
      (multiplyInt (unsignedZ dh) (unsignedZ quotient))
      radixNat →
  (remainder : Word64) →
  unsignedZ remainder ≡
    euclideanModuloPositive
      (addInt (unsignedZ lowProduct) (unsignedZ dl))
      radixNat →
  AfterRemainder quotient dh dl remainder

reciprocal-word-3by2'vc : Set
reciprocal-word-3by2'vc =
  (dh dl : Word64) →
  halfRadixZ ≤Z unsignedZ dh →
  halfRadixZ ≤Z unsignedZ dh
  ∧
  ((quotient : Word64) →
    reciprocal quotient dh →
    AfterLowProduct quotient dh dl)
