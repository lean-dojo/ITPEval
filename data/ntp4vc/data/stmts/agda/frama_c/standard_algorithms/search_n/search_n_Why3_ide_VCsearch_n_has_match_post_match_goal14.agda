-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/search_n/search_n_Why3_ide_VCsearch_n_has_match_post_match_goal14:
-- under the stated integer-range, memory-validity, linkedness, and search-state
-- assumptions, the searched value is constant on the resulting match range.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module search_n_Why3_ide_VCsearch_n_has_match_post_match_goal14 where

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    evidence : P value

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

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

PHasConstantSubrange :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PHasConstantSubrange integer-memory a upper length value =
  Exists Int λ first-index →
    let last-index = addInt length first-index
    in
    (zeroZ ≤Z first-index) ∧
    (last-index ≤Z upper) ∧
    PConstantRange
      integer-memory
      a
      first-index
      last-index
      value

Goal14 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Uint32Conversion →
  Set
Goal14 region linked conversion =
  (integer-memory : Addr → Int) →
  (a : Addr) →
  (i i₆ i₁ i₂ : Int) →
  (allocation : Int → Int) →
  (i₃ i₄ i₅ i₇ : Int) →
  let
    x = integer-memory (shift a (subtractInt i oneZ))
    x₁ = addInt oneZ i₆
    x₂ = addInt i₁ i₂
    a₁ = shift a i₆
    x₃ = toUint32 conversion x₁
  in
  region (base a) ≤Z zeroZ →
  linked allocation →
  IsUint32 i →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 i₃ →
  IsUint32 i₄ →
  IsUint32 i₅ →
  IsUint32 i₆ →
  IsSint32 i₇ →
  PHasConstantSubrange integer-memory a i₄ i₂ i₇ →
  ValidRD allocation (shift a zeroZ) i₄ →
  IsSint32 x →
  IfSet
    (intLess zeroZ i₂)
    (IfSet
      (intLessOrEqual i₂ i₄)
      ((i₅ ≡ i₃) ∧
        (i₅ ≡ i₄) ∧
        (i ≤Z x₁) ∧
        PConstantRange integer-memory a i i₆ i₇ ∧
        Not (PHasConstantSubrange integer-memory a i₆ i₂ i₇) ∧
        IfSet
          (intLess i₆ i₅)
          ((i₁ ≡ i) ∧
            (x₂ ≡ x₁) ∧
            (integer-memory a₁ ≡ i₇) ∧
            (i₁ ≤Z x₃) ∧
            (i₆ ≤Z uint32MaximumMinusOne) ∧
            (x₃ ≤Z addInt uint32Maximum i₁) ∧
            ValidRD allocation a₁ oneZ)
          (i₅ ≡ i₁) ∧
        (zeroZ <Z i → x ≠ i₇))
      (i₄ ≡ i₁))
    (i₁ ≡ zeroZ) →
  PConstantRange integer-memory a i₁ x₂ i₇

search-n-has-match-post-match-goal14 : Set₁
search-n-has-match-post-match-goal14 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (conversion : Uint32Conversion) →
  Goal14 region linked conversion
