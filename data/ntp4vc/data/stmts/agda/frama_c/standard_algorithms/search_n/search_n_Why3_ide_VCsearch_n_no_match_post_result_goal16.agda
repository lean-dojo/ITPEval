-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/search_n/search_n_Why3_ide_VCsearch_n_no_match_post_result_goal16:
-- under the stated integer-range, memory-validity, linkedness, and
-- constant-subrange assumptions, the no-match search result equals the
-- recorded terminal index. This file contains no proof.

{-# OPTIONS --safe #-}

module search_n_Why3_ide_VCsearch_n_no_match_post_result_goal16 where

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

ifSet : Bool → Set → Set → Set
ifSet true yes _ = yes
ifSet false _ no = no

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

uint32MaximumMinusOne uint32Upper : Int
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

record Uint32Projection : Set where
  field
    toUint32 : Int → Int

    toUint32-in-range :
      (x : Int) →
      IsUint32 (toUint32 x)

    toUint32-identity :
      (x : Int) →
      IsUint32 x →
      toUint32 x ≡ x

open Uint32Projection

ConstantRange :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
ConstantRange integer-memory a first last value =
  (index : Int) →
  first ≤Z index →
  index <Z last →
  integer-memory (shift a index) ≡ value

HasConstantSubrange :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
HasConstantSubrange integer-memory a m n value =
  Exists Int λ start →
    let endpoint = addInt n start
    in
    (zeroZ ≤Z start) ∧
    (endpoint ≤Z m) ∧
    ConstantRange integer-memory a start endpoint value

Goal16 :
  Uint32Projection →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal16 conversion region linked =
  (integer-memory : Addr → Int) →
  (a : Addr) →
  (i i₇ i₃ : Int) →
  (allocation : Int → Int) →
  (i₁ i₂ i₄ i₅ i₆ i₈ : Int) →
  let
    x = integer-memory (shift a (subtractInt i oneZ))
    x₁ = addInt oneZ i₇
    a₁ = shift a i₇
    x₂ = addInt i₃ (toUint32 conversion x₁)
    branch-state =
      ifSet
        (intLess zeroZ i₃)
        (ifSet
          (intLessOrEqual i₃ i₅)
          ((i₅ ≡ i₄) ∧
            (i₆ ≡ i₄) ∧
            (i₆ ≡ i₅) ∧
            (i ≤Z x₁) ∧
            ConstantRange integer-memory a i i₇ i₈ ∧
            Not
              (HasConstantSubrange
                integer-memory
                a
                i₇
                i₃
                i₈) ∧
            (ifSet
              (intLess i₇ i₅)
              ((addInt i i₃ ≡ x₁) ∧
                (addInt i₁ i₃ ≡ x₁) ∧
                (addInt i₂ i₃ ≡ x₁) ∧
                (integer-memory a₁ ≡ i₈) ∧
                (i₇ <Z x₂) ∧
                (i₇ ≤Z uint32MaximumMinusOne) ∧
                (x₂ ≤Z addInt uint32Upper i₇) ∧
                ValidRD allocation a₁ oneZ)
              (i₅ ≡ i₂)) ∧
            (zeroZ <Z i → Not (x ≡ i₈)))
          (i₅ ≡ i₂))
        (i₂ ≡ zeroZ)
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
  IsUint32 i₇ →
  IsSint32 i₈ →
  Not (HasConstantSubrange integer-memory a i₅ i₃ i₈) →
  ValidRD allocation (shift a zeroZ) i₅ →
  IsSint32 x →
  branch-state →
  i₅ ≡ i₂

search-n-no-match-post-result-goal16 : Set₁
search-n-no-match-post-result-goal16 =
  (conversion : Uint32Projection) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal16 conversion region linked
