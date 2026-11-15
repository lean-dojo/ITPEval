-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/klibc_string/memmem_Why3_ide_VCmemmem_disjoint_occr_not_occur_err_part1_goal1:
-- under the stated nonnegative-length, memory-region, linkedness, unsigned
-- 32-bit, writable-memory, and separation assumptions, either a length is
-- zero, the first length is smaller, the nonzero lengths are oppositely
-- ordered, or there is an offset at which the compared memory ranges agree
-- throughout the relevant indices. This file contains no proof.

{-# OPTIONS --safe #-}

module memmem-Why3-ide-VCmemmem-disjoint-occr-not-occur-err-part1-goal1 where

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

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

zeroZ uint32Upper : Int
zeroZ = pos zero
uint32Upper = pos 4294967296

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

Separated : Addr → Int → Addr → Int → Set
Separated p a q b =
  Either
    (a ≤Z zeroZ)
    (Either
      (b ≤Z zeroZ)
      (Either
        (base p ≠ base q)
        (Either
          (addInt (offset q) b ≤Z offset p)
          (addInt (offset p) a ≤Z offset q))))

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

Goal1 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal1 region linked =
  (a₂ a₃ : Addr) →
  (i i₁ : Int) →
  (allocation : Int → Int) →
  (scalarMemory : Addr → Int) →
  (a₁ a : Addr) →
  let
    a₄ = shift a₂ zeroZ
    a₅ = shift a₃ zeroZ
  in
  zeroZ ≤Z i →
  zeroZ ≤Z i₁ →
  region (base a₂) ≤Z zeroZ →
  region (base a₃) ≤Z zeroZ →
  linked allocation →
  IsUint32 i →
  IsUint32 i₁ →
  ValidRW allocation a₄ i₁ →
  ValidRW allocation a₅ i →
  Separated a₅ i a₄ i₁ →
  Either
    (i ≡ zeroZ)
    (Either
      (i₁ ≡ zeroZ)
      (Either
        (i <Z i₁)
        (Either
          ((i ≠ zeroZ) ∧ (i₁ ≠ zeroZ) ∧ (i₁ ≤Z i))
          (Exists Int
            (λ i₂ →
              (zeroZ ≤Z i₂) ∧
              (addInt i₂ i₁ ≤Z i) ∧
              ((i₃ : Int) →
                Either
                  (scalarMemory (shift a₁ (addInt i₃ i₂))
                    ≡ scalarMemory (shift a i₃))
                  (Either
                    (i₃ <Z zeroZ)
                    (i₁ ≤Z i₃))))))))

memmem-disjoint-occr-not-occur-err-part1-goal1 : Set₁
memmem-disjoint-occr-not-occur-err-part1-goal1 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal1 region linked
