-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_call_lower_bound_pre_sorted_goal26:
-- under the stated integer-range, sortedness, bound, memory-validity,
-- region, and linkedness assumptions, the prefix passed to lower_bound is sorted.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module equal_range_Why3_ide_VCequal_range_call_lower_bound_pre_sorted_goal26 where

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

Goal26 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Uint32Conversion →
  Set
Goal26 region linked conversion =
  (i₂ : Int) →
  (i₃ : Int) →
  (a : Addr) →
  (integer-memory : Addr → Int) →
  (i₁ : Int) →
  (searched : Int) →
  (allocation : Int → Int) →
  let
    x = subtractInt i₂ i₃
    x₁ = cdivTwo x
    x₂ = addInt i₃ x₁
    a₁ = shiftSint32 a x₂
    x₃ = integer-memory a₁
    x₄ = addInt i₃ (toUint32 conversion (cdivTwo (toUint32 conversion x)))
  in
  i₂ ≤Z i₁ →
  i₃ ≤Z i₂ →
  zeroZ ≤Z i₃ →
  i₃ <Z i₂ →
  region (base a) ≤Z zeroZ →
  zeroZ ≤Z x₁ →
  x₃ ≤Z searched →
  zeroZ ≤Z x₄ →
  searched ≤Z x₃ →
  i₂ ≤Z addInt uint32Maximum i₃ →
  x₁ ≤Z uint32Maximum →
  x₄ ≤Z uint32Maximum →
  linked allocation →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 i₃ →
  IsSint32 searched →
  PSorted integer-memory a zeroZ i₁ →
  PStrictUpperBound integer-memory a zeroZ i₃ searched →
  PStrictLowerBound integer-memory a i₂ i₁ searched →
  ValidRD allocation (shiftSint32 a zeroZ) i₁ →
  IsUint32 x₂ →
  IsSint32 x₃ →
  ValidRD allocation a₁ oneZ →
  PSorted integer-memory (shiftSint32 a i₃) zeroZ x₁

equal-range-call-lower-bound-pre-sorted-goal26 : Set₁
equal-range-call-lower-bound-pre-sorted-goal26 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (conversion : Uint32Conversion) →
  Goal26 region linked conversion
