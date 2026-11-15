-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_call_upper_bound_pre_sorted_goal28:
-- under the stated integer-range, signed-32-bit address-shifting, sortedness,
-- bound, memory-validity, region, and linkedness assumptions, the suffix
-- passed to upper_bound is sorted.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module equal_range_Why3_ide_VCequal_range_call_upper_bound_pre_sorted_goal28 where

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

zeroZ oneZ uint32Maximum uint32Upper signed32Lower signed32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
uint32Maximum = pos 4294967295
uint32Upper = pos 4294967296
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

Goal28 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Uint32Conversion →
  Set
Goal28 region linked conversion =
  (i₁ : Int) →
  (i₄ : Int) →
  (i₃ : Int) →
  (a : Addr) →
  (integer-memory : Addr → Int) →
  (i₂ : Int) →
  (searched : Int) →
  (allocation : Int → Int) →
  let
    x = addInt i₁ i₄
    x₂ = subtractInt i₃ i₄
    x₃ = cdivTwo x₂
    x₄ = addInt i₄ x₃
    a₁ = shiftSint32 a x₄
    x₅ = integer-memory a₁
    x₆ = addInt i₄ (toUint32 conversion (cdivTwo (toUint32 conversion x₂)))
    a₂ = shiftSint32 a i₄
    x₇ = addInt (addInt oneZ i₄) x₃
  in
  zeroZ ≤Z i₁ →
  i₃ ≤Z i₂ →
  i₄ ≤Z i₃ →
  zeroZ ≤Z i₄ →
  i₄ <Z i₃ →
  zeroZ ≤Z x →
  region (base a) ≤Z zeroZ →
  zeroZ ≤Z x₃ →
  i₁ ≤Z x₃ →
  x₄ <Z i₃ →
  x₅ ≤Z searched →
  zeroZ ≤Z x₆ →
  searched ≤Z x₅ →
  x ≤Z uint32Maximum →
  i₃ ≤Z addInt uint32Maximum i₄ →
  x₃ ≤Z uint32Maximum →
  x₄ ≤Z pos 4294967294 →
  i₃ ≤Z addInt (addInt uint32Upper i₄) x₃ →
  x₆ ≤Z uint32Maximum →
  linked allocation →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 i₃ →
  IsUint32 i₄ →
  IsSint32 searched →
  PSorted integer-memory a zeroZ i₂ →
  PStrictUpperBound integer-memory a zeroZ i₄ searched →
  PStrictLowerBound integer-memory a i₃ i₂ searched →
  ValidRD allocation (shiftSint32 a zeroZ) i₂ →
  ValidRD allocation a₂ x₃ →
  PSorted integer-memory a₂ zeroZ x₃ →
  IsUint32 x₄ →
  IsUint32 x₇ →
  IsSint32 x₅ →
  ValidRD allocation a₁ oneZ →
  PStrictUpperBound integer-memory a₂ zeroZ i₁ x₅ →
  PLowerBound integer-memory a₂ i₁ x₃ x₅ →
  PSorted
    integer-memory
    (shiftSint32 a x₇)
    zeroZ
    (subtractInt (subtractInt (subtractInt i₃ oneZ) i₄) x₃)

equal-range-call-upper-bound-pre-sorted-goal28 : Set₁
equal-range-call-upper-bound-pre-sorted-goal28 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (conversion : Uint32Conversion) →
  Goal28 region linked conversion
