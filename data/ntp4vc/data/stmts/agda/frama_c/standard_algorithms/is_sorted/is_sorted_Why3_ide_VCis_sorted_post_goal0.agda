-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/is_sorted/is_sorted_Why3_ide_VCis_sorted_post_goal0:
-- under the stated integer-range, memory-validity, region, linkedness, and
-- loop-state assumptions, the array prefix is sorted exactly when the
-- is_sorted result integer is nonzero. This file contains no proof.

{-# OPTIONS --safe #-}

module is_sorted_Why3_ide_VCis_sorted_post_goal0 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≤Z_ _<Z_ _↔_
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

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

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

zeroZ oneZ twoZ uint32Penultimate uint32Upper signed32Lower signed32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
uint32Penultimate = pos 4294967294
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

PWeaklySorted :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PWeaklySorted integer-memory a lower upper =
  (index : Int) →
  lower ≤Z index →
  addInt twoZ index ≤Z upper →
  integer-memory (shift a index)
    ≤Z
  integer-memory (shift a (addInt oneZ index))

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

Goal0 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Uint32Conversion →
  Set
Goal0 region linked conversion =
  (i₂ : Int) →
  (a : Addr) →
  (allocation : Int → Int) →
  (i : Int) →
  (result : Int) →
  (p : Bool) →
  (integer-memory : Addr → Int) →
  let
    x = addInt oneZ i₂
    a₁ = shift a i₂
  in
  region (base a) ≤Z zeroZ →
  linked allocation →
  IsUint32 i →
  IsUint32 i₂ →
  IsSint32 result →
  ValidRD allocation (shift a zeroZ) i →
  IfSet
    (intLess zeroZ i)
    ((p ≡ false) ∧
      PWeaklySorted integer-memory a zeroZ x ∧
      IfSet
        (intLessOrEqual (addInt twoZ i₂) i)
        ((result ≡ zeroZ) ∧
          (integer-memory (shift a x) <Z integer-memory a₁) ∧
          (i₂ ≤Z uint32Penultimate) ∧
          ValidRD allocation a₁ oneZ ∧
          ValidRD allocation
            (shift a (toUint32 conversion x))
            oneZ)
        (result ≡ oneZ))
    (result ≡ oneZ) →
  PSorted integer-memory a zeroZ i ↔ Not (result ≡ zeroZ)

is-sorted-post-goal0 : Set₁
is-sorted-post-goal0 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (conversion : Uint32Conversion) →
  Goal0 region linked conversion
