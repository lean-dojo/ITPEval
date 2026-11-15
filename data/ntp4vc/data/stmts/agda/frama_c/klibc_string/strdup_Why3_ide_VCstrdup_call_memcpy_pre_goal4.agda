-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/klibc_string/strdup_Why3_ide_VCstrdup_call_memcpy_pre_goal4:
-- under the stated string-length, signed-integer, allocation, linkedness,
-- constancy, and writable-memory assumptions for strdup, the source and
-- destination byte ranges passed to memcpy are separated. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module strdup_Why3_ide_VCstrdup_call_memcpy_pre_goal4 where

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

zeroZ oneZ signed32Lower signed32Upper uint32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
uint32Upper = pos 4294967296

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

zeroAddr : Addr
zeroAddr = addr zeroZ zeroZ

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

PLengthOfStrIs :
  (Int → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Set
PLengthOfStrIs allocation memory string n =
  (memory (shift string n) ≡ zeroZ) ∧
  (zeroZ ≤Z n) ∧
  ValidRW allocation (shift string zeroZ) (addInt oneZ n) ∧
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z n →
    memory (shift string index) ≠ zeroZ)

record StringLength : Set where
  field
    length : (Addr → Int) → Addr → Int

    length-of-string :
      (allocation : Int → Int) →
      (memory : Addr → Int) →
      (string : Addr) →
      (n : Int) →
      PLengthOfStrIs allocation memory string n →
      length memory string ≡ n

open StringLength

Goal4 :
  Uint32Projection →
  StringLength →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal4 conversion lengths region linked sconst =
  (character-memory : Addr → Int) →
  (source destination : Addr) →
  (allocation : Int → Int) →
  (i i₁ i₂ : Int) →
  let
    source-length = length lengths character-memory source
    byte-count = addInt oneZ source-length
    converted-byte-count = toUint32 conversion byte-count
    destination-start = shift destination zeroZ
  in
  zeroAddr ≠ destination →
  converted-byte-count ≠ zeroZ →
  region (base source) ≤Z zeroZ →
  linked allocation →
  sconst character-memory →
  IsSint32 source-length →
  PLengthOfStrIs allocation character-memory source i →
  PLengthOfStrIs allocation character-memory source i₁ →
  PLengthOfStrIs allocation character-memory source i₂ →
  IsSint32 byte-count →
  (zeroZ <Z converted-byte-count →
    ValidRW allocation destination-start converted-byte-count) →
  Separated
    (shift source zeroZ)
    converted-byte-count
    destination-start
    converted-byte-count

strdup-call-memcpy-pre-goal4 : Set₁
strdup-call-memcpy-pre-goal4 =
  (conversion : Uint32Projection) →
  (lengths : StringLength) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal4 conversion lengths region linked sconst
