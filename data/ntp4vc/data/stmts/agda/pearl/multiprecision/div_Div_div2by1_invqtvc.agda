-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/div_Div_div2by1_invqtvc: the verification condition
-- for reciprocal-based division of a two-limb unsigned integer by a
-- normalized 64-bit divisor, including quotient correction and remainder
-- bounds. This file contains no proof.

{-# OPTIONS --safe #-}

module div_Div_div2by1_invqtvc where

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

DivisionResult :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
DivisionResult quotient remainder d uh ul =
  addInt
    (multiplyInt (unsignedZ quotient) (unsignedZ d))
    (unsignedZ remainder)
    ≡
  addInt (unsignedZ ul) (multiplyInt radixZ (unsignedZ uh))
  ∧ zeroZ ≤Z unsignedZ remainder
  ∧ unsignedZ remainder <Z unsignedZ d

AfterO6 :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
AfterO6 d uh ul o5 o4 =
  (o6 : Word64) →
  unsignedZ o6 ≡ subtractInt (unsignedZ o4) (unsignedZ d) →
  DivisionResult o5 o6 d uh ul

AfterO5 :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
AfterO5 d uh ul o3 o4 =
  (o5 : Word64) →
  unsignedZ o5 ≡ addInt (unsignedZ o3) oneZ →
  UInt64InBounds
    (subtractInt (unsignedZ o4) (unsignedZ d))
  ∧ AfterO6 d uh ul o5 o4

FirstCorrectionAfterO4 :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
FirstCorrectionAfterO4 d uh ul o3 o2 =
  (o4 : Word64) →
  unsignedZ o4 ≡
    euclideanModuloPositive
      (addInt (unsignedZ o2) (unsignedZ d))
      radixNat →
  IfSet
    (intLessOrEqual (unsignedZ d) (unsignedZ o4))
    (UInt64InBounds (addInt (unsignedZ o3) oneZ)
     ∧ AfterO5 d uh ul o3 o4)
    (DivisionResult o3 o4 d uh ul)

FirstCorrectionAfterO3 :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
FirstCorrectionAfterO3 d uh ul o1 o2 =
  (o3 : Word64) →
  unsignedZ o3 ≡
    euclideanModuloPositive
      (subtractInt (unsignedZ o1) oneZ)
      radixNat →
  FirstCorrectionAfterO4 d uh ul o3 o2

SecondCorrectionAfterO4 :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
SecondCorrectionAfterO4 d uh ul o3 o2 =
  (o4 : Word64) →
  unsignedZ o4 ≡ subtractInt (unsignedZ o2) (unsignedZ d) →
  DivisionResult o3 o4 d uh ul

SecondCorrectionAfterO3 :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
SecondCorrectionAfterO3 d uh ul o1 o2 =
  (o3 : Word64) →
  unsignedZ o3 ≡ addInt (unsignedZ o1) oneZ →
  UInt64InBounds
    (subtractInt (unsignedZ o2) (unsignedZ d))
  ∧ SecondCorrectionAfterO4 d uh ul o3 o2

CorrectionBranches :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
CorrectionBranches d uh ul sl o1 o2 =
  IfSet
    (intLess (unsignedZ sl) (unsignedZ o2))
    (FirstCorrectionAfterO3 d uh ul o1 o2)
    (IfSet
      (intLessOrEqual (unsignedZ d) (unsignedZ o2))
      (UInt64InBounds (addInt (unsignedZ o1) oneZ)
       ∧ SecondCorrectionAfterO3 d uh ul o1 o2)
      (DivisionResult o1 o2 d uh ul))

AfterO2 :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
AfterO2 d uh ul sl o1 p =
  (o2 : Word64) →
  unsignedZ o2 ≡
    euclideanModuloPositive
      (subtractInt (unsignedZ ul) (unsignedZ p))
      radixNat →
  CorrectionBranches d uh ul sl o1 o2

AfterP :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
AfterP d uh ul sl o1 =
  (p : Word64) →
  unsignedZ p ≡
    euclideanModuloPositive
      (multiplyInt (unsignedZ o1) (unsignedZ d))
      radixNat →
  AfterO2 d uh ul sl o1 p

AfterO1 :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
AfterO1 d uh ul sl sh =
  (o1 : Word64) →
  unsignedZ o1 ≡
    euclideanModuloPositive
      (addInt (unsignedZ sh) oneZ)
      radixNat →
  AfterP d uh ul sl o1

HighAddObligation :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
HighAddObligation d uh h ul sl c =
  (sh c′ : Word64) →
  (addInt
    (unsignedZ sh)
    (multiplyInt radixZ (unsignedZ c′))
    ≡
   addInt
    (addInt (unsignedZ uh) (unsignedZ h))
    (unsignedZ c)
   ∧ zeroZ ≤Z unsignedZ c′
   ∧ unsignedZ c′ ≤Z oneZ) →
  AfterO1 d uh ul sl sh

LowAddObligation :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
LowAddObligation d uh l h ul =
  (sl c : Word64) →
  (addInt
    (unsignedZ sl)
    (multiplyInt radixZ (unsignedZ c))
    ≡
   addInt
    (addInt (unsignedZ l) (unsignedZ ul))
    zeroZ
   ∧ zeroZ ≤Z unsignedZ c
   ∧ unsignedZ c ≤Z oneZ) →
  (zeroZ ≤Z unsignedZ c ∧ unsignedZ c ≤Z oneZ)
  ∧ HighAddObligation d uh h ul sl c

div2by1-inv'vc : Set
div2by1-inv'vc =
  (d uh v l h ul : Word64) →
  halfRadixZ ≤Z unsignedZ d →
  unsignedZ uh <Z unsignedZ d →
  reciprocal v d →
  addInt
    (unsignedZ l)
    (multiplyInt radixZ (unsignedZ h))
    ≡
  multiplyInt (unsignedZ v) (unsignedZ uh) →
  zeroZ ≤Z zeroZ
  ∧ zeroZ ≤Z oneZ
  ∧ LowAddObligation d uh l h ul
