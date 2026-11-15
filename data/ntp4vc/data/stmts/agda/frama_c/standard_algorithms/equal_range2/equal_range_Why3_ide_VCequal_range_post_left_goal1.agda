-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_post_left_goal1:
-- under the stated integer-range, sortedness, bound, memory-validity, region,
-- linkedness, and equal-range state assumptions, the prefix before the left
-- endpoint is strictly below the value at the selected midpoint.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module equal_range_Why3_ide_VCequal_range_post_left_goal1 where

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
  integer-memory (shift a left) ≤Z integer-memory (shift a right)

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

Goal1 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Uint32Conversion →
  Set
Goal1 region linked conversion =
  (s : SizeTypePair) →
  (i₁ i₃ : Int) →
  (a : Addr) →
  (integer-memory : Addr → Int) →
  (i₂ searched : Int) →
  (allocation : Int → Int) →
  let
    x = secondComponent s
    x₁ = firstComponent s
    x₂ = addInt i₁ i₃
    x₄ = subtractInt x₂ x₁
    x₅ = cdivTwo x₄
    x₆ = addInt x₁ x₅
    x₇ = addInt x₁ (toUint32 conversion (cdivTwo (toUint32 conversion x₄)))
    x₉ = subtractInt (addInt x₁ x₅) i₁
    a₁ = shiftSint32 a x₉
    x₁₀ = integer-memory a₁
    x₁₁ = subtractInt x₁ i₁
    a₂ = shiftSint32 a x₁₁
    x₁₂ = subtractInt (addInt (addInt oneZ x₁) x₅) i₁
    x₁₄ =
      subtractInt
        (subtractInt
          (subtractInt (addInt i₁ x) oneZ)
          x₁)
        x₅
    a₃ = shiftSint32 a x₁₂
    x₁₅ =
      subtractInt
        (subtractInt
          (subtractInt (addInt i₁ i₃) oneZ)
          x₁)
        x₅
  in
  zeroZ ≤Z i₁ →
  i₃ ≤Z i₂ →
  x ≤Z i₃ →
  zeroZ ≤Z x₁ →
  i₁ ≤Z x₁ →
  zeroZ ≤Z x →
  x₁ <Z x₂ →
  region (base a) ≤Z zeroZ →
  zeroZ ≤Z x₅ →
  i₁ ≤Z x₅ →
  x₆ <Z x₂ →
  x₆ <Z addInt i₁ x →
  i₁ ≤Z x₇ →
  x₁₀ ≤Z searched →
  searched ≤Z x₁₀ →
  x₁ ≤Z uint32Maximum →
  x ≤Z uint32Maximum →
  x₂ ≤Z addInt uint32Maximum x₁ →
  x₅ ≤Z uint32Maximum →
  x₆ ≤Z addInt uint32MaximumMinusOne i₁ →
  x₂ ≤Z addInt (addInt uint32Upper x₁) x₅ →
  x₇ ≤Z addInt uint32Maximum i₁ →
  IsSizeTypePair s →
  linked allocation →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 i₃ →
  IsSint32 searched →
  IsUint32 x₁ →
  IsUint32 x →
  PSorted integer-memory a zeroZ i₂ →
  IsUint32 x₁₁ →
  PStrictLowerBound integer-memory a i₃ i₂ searched →
  ValidRD allocation (shiftSint32 a zeroZ) i₂ →
  PStrictUpperBound integer-memory a zeroZ x₁₁ searched →
  ValidRD allocation a₂ x₅ →
  PSorted integer-memory a₂ zeroZ x₅ →
  IsUint32 x₉ →
  IsUint32 x₁₂ →
  IsUint32 x₁₄ →
  IsSint32 x₁₀ →
  ValidRD allocation a₁ oneZ →
  ValidRD allocation a₃ x₁₅ →
  PSorted integer-memory a₃ zeroZ x₁₅ →
  PStrictUpperBound integer-memory a₂ zeroZ i₁ x₁₀ →
  PStrictLowerBound integer-memory a₃ x₁₄ x₁₅ x₁₀ →
  PLowerBound integer-memory a₂ i₁ x₅ x₁₀ →
  PUpperBound integer-memory a₃ zeroZ x₁₄ x₁₀ →
  PStrictUpperBound integer-memory a zeroZ x₁ x₁₀

equal-range-post-left-goal1 : Set₁
equal-range-post-left-goal1 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (conversion : Uint32Conversion) →
  Goal1 region linked conversion
