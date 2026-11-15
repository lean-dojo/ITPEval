-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/binary_search/binary_search_Why3_ide_VCbinary_search_post_result_goal0:
-- under the stated integer-range, sortedness, bound, memory-validity,
-- region, and linkedness assumptions, the searched value occurs in the
-- array exactly when the binary-search result flag is nonzero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module binary_search_Why3_ide_VCbinary_search_post_result_goal0 where

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

uint32Upper signed32Lower signed32Upper : Int
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

Goal0 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal0 region linked =
  (a : Addr) →
  (i₂ : Int) →
  (integer-memory : Addr → Int) →
  (i₁ : Int) →
  (allocation : Int → Int) →
  (searched : Int) →
  (result : Int) →
  let
    a₁ = shift a i₂
    x = integer-memory a₁
  in
  i₂ ≤Z i₁ →
  zeroZ ≤Z i₂ →
  region (base a) ≤Z zeroZ →
  linked allocation →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsSint32 searched →
  IsSint32 result →
  PSorted integer-memory a zeroZ i₁ →
  IsSint32 x →
  PLowerBound integer-memory a i₂ i₁ searched →
  PStrictUpperBound integer-memory a zeroZ i₂ searched →
  ValidRD allocation (shift a zeroZ) i₁ →
  IfSet
    (intLess i₂ i₁)
    (ValidRD allocation a₁ oneZ ∧
      IfSet
        (intLessOrEqual x searched)
        (result ≡ oneZ)
        (result ≡ zeroZ))
    (result ≡ zeroZ) →
  Exists Int
    (λ i₄ →
      (integer-memory (shift a i₄) ≡ searched) ∧
      (zeroZ ≤Z i₄) ∧
      (i₄ <Z i₁))
    ↔
  Not (result ≡ zeroZ)

binary-search-post-result-goal0 : Set₁
binary-search-post-result-goal0 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal0 region linked
