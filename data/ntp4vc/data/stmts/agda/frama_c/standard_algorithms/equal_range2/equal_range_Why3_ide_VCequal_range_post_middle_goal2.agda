-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_post_middle_goal2:
-- under the stated integer-range, sortedness, bound, memory-validity, region,
-- linkedness, and equal-range state assumptions, the selected middle range is
-- constant at the searched value. This file contains no proof.

{-# OPTIONS --safe #-}

module equal_range_Why3_ide_VCequal_range_post_middle_goal2 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not proposition = proposition → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

negateInt : Int → Int
negateInt (pos zero) = pos zero
negateInt (pos (suc n)) = negsuc n
negateInt (negsuc n) = pos (suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

negativeNat : Nat → Int
negativeNat zero = pos zero
negativeNat (suc n) = negsuc n

cdivTwo : Int → Int
cdivTwo (pos n) = pos (halfNat n)
cdivTwo (negsuc n) = negativeNat (halfNat (suc n))

zeroZ oneZ uint32Maximum uint32MaximumMinusOne uint32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
uint32Maximum = pos 4294967295
uint32MaximumMinusOne = pos 4294967294
uint32Upper = pos 4294967296

signed32Lower signed32Upper : Int
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

fourTimes : Int → Int
fourTimes k = addInt (addInt k k) (addInt k k)

shiftSint32 : Addr → Int → Addr
shiftSint32 p k = shift p k

ValidRD : (Int → Int) → Addr → Int → Set
ValidRD allocation p n =
  zeroZ <Z n →
  (zeroZ ≠ base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

record Uint32Conversion : Set where
  field
    toUint32 : Int → Int
    resultInRange : (x : Int) → IsUint32 (toUint32 x)
    identityInRange : (x : Int) → IsUint32 x → toUint32 x ≡ x

open Uint32Conversion

record SizeTypePair : Set where
  constructor sizeTypePair
  field
    firstComponent  : Int
    secondComponent : Int

open SizeTypePair

IsSizeTypePair : SizeTypePair → Set
IsSizeTypePair pair =
  IsUint32 (firstComponent pair) ∧
  IsUint32 (secondComponent pair)

PSorted :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PSorted integer-memory a lower upper =
  (left right : Int) →
  right <Z upper →
  lower ≤Z left →
  left <Z right →
  integer-memory (shift a left) ≤Z
  integer-memory (shift a right)

PLowerBound :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PLowerBound integer-memory a lower upper searched =
  (index : Int) →
  lower ≤Z index →
  index <Z upper →
  searched ≤Z integer-memory (shift a index)

PStrictLowerBound :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PStrictLowerBound integer-memory a lower upper searched =
  (index : Int) →
  lower ≤Z index →
  index <Z upper →
  searched <Z integer-memory (shift a index)

PStrictUpperBound :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PStrictUpperBound integer-memory a lower upper searched =
  (index : Int) →
  lower ≤Z index →
  index <Z upper →
  integer-memory (shift a index) <Z searched

PUpperBound :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PUpperBound integer-memory a lower upper searched =
  (index : Int) →
  lower ≤Z index →
  index <Z upper →
  integer-memory (shift a index) ≤Z searched

PConstantRange :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PConstantRange integer-memory a first-index last-index value =
  (index : Int) →
  first-index ≤Z index →
  index <Z last-index →
  integer-memory (shift a index) ≡ value

Goal2 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Uint32Conversion →
  Set
Goal2 region linked conversion =
  (s : SizeTypePair) →
  (i₈ i₁₀ : Int) →
  (a : Addr) →
  (integer-memory : Addr → Int) →
  (i₇ i₁₁ : Int) →
  (allocation : Int → Int) →
  (i₁ i₂ i₃ i₄ i₅ i₆ i₉ searched : Int) →
  (p₁ p₂ p₃ p : Bool) →
  let
    x = firstComponent s
    x₂ = subtractInt i₈ i₁₀
    x₃ = cdivTwo x₂
    x₄ = addInt i₁₀ x₃
    x₅ = secondComponent s
    a₁ = shiftSint32 a x₄
    x₆ = integer-memory a₁
    x₇ = addInt i₁₀ (toUint32 conversion (cdivTwo (toUint32 conversion x₂)))
    a₂ = shiftSint32 a i₁₀
    a₃ = shiftSint32 a (addInt (addInt oneZ i₁₀) x₃)
    x₉ = subtractInt (subtractInt (subtractInt i₈ oneZ) i₁₀) x₃
    x₁₀ = subtractInt x i₁₀
    x₁₁ = subtractInt (subtractInt (subtractInt x₅ oneZ) i₁₀) x₃
  in
  i₈ ≤Z i₇ →
  i₁₁ ≤Z i₈ →
  zeroZ ≤Z i₁₁ →
  region (base a) ≤Z zeroZ →
  IsSizeTypePair s →
  linked allocation →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 i₃ →
  IsUint32 i₄ →
  IsUint32 i₅ →
  IsUint32 i₆ →
  IsUint32 i₇ →
  IsUint32 i₈ →
  IsUint32 i₉ →
  IsUint32 i₁₀ →
  IsUint32 i₁₁ →
  IsSint32 searched →
  PSorted integer-memory a zeroZ i₇ →
  PStrictUpperBound integer-memory a zeroZ i₁₁ searched →
  PStrictLowerBound integer-memory a i₈ i₇ searched →
  ValidRD allocation (shiftSint32 a zeroZ) i₇ →
  IfSet
    (intLess i₁₁ i₈)
    ((p₁ ≡ false) ∧
      (p₂ ≡ false) ∧
      (p₃ ≡ false) ∧
      (i₂ ≡ i₁) ∧
      (i₅ ≡ i₄) ∧
      (i₁₀ ≡ i₉) ∧
      (i₁₁ ≡ i₁₀) ∧
      (x ≡ addInt i₃ i₁₀) ∧
      (x ≡ addInt i₆ i₁₀) ∧
      (x₄ ≡ i₄) ∧
      (x₄ ≡ i₅) ∧
      (x₅ ≡ addInt (addInt (addInt oneZ i₁) i₁₀) x₃) ∧
      (x₅ ≡ addInt (addInt (addInt oneZ i₂) i₁₀) x₃) ∧
      (x₅ ≤Z i₈) ∧
      (zeroZ ≤Z x) ∧
      (i₁₀ ≤Z x) ∧
      (zeroZ ≤Z x₅) ∧
      (zeroZ ≤Z x₃) ∧
      (x₄ <Z i₈) ∧
      (x ≤Z x₄) ∧
      (x₄ <Z x₅) ∧
      (x₆ ≤Z searched) ∧
      (zeroZ ≤Z x₇) ∧
      (searched ≤Z x₆) ∧
      (x ≤Z uint32Maximum) ∧
      (x₅ ≤Z uint32Maximum) ∧
      (i₈ ≤Z addInt uint32Maximum i₁₀) ∧
      (x₃ ≤Z uint32Maximum) ∧
      (x₄ ≤Z uint32MaximumMinusOne) ∧
      (i₈ ≤Z addInt (addInt uint32Upper i₁₀) x₃) ∧
      (x₇ ≤Z uint32Maximum) ∧
      ValidRD allocation a₂ x₃ ∧
      PSorted integer-memory a₂ zeroZ x₃ ∧
      ValidRD allocation a₁ oneZ ∧
      ValidRD allocation a₃ x₉ ∧
      PSorted integer-memory a₃ zeroZ x₉ ∧
      PStrictUpperBound integer-memory a₂ zeroZ x₁₀ x₆ ∧
      PStrictLowerBound integer-memory a₃ x₁₁ x₉ x₆ ∧
      PLowerBound integer-memory a₂ x₁₀ x₃ x₆ ∧
      PUpperBound integer-memory a₃ zeroZ x₁₁ x₆)
    ((p ≡ false) ∧
      (x ≡ i₁₁) ∧
      (x₅ ≡ x)) →
  PConstantRange integer-memory a x x₅ searched

equal-range-post-middle-goal2 : Set₁
equal-range-post-middle-goal2 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (conversion : Uint32Conversion) →
  Goal2 region linked conversion
