-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/klibc_string/strndup_Why3_ide_VCstrndup_call_memcpy_pre_4_goal5:
-- under the stated unsigned-integer, string-content, allocation, linkedness,
-- constancy, and writable-memory assumptions for strndup, the source range
-- of length i₁ is writable. This file contains no proof.

{-# OPTIONS --safe #-}

module strndup-Why3-ide-VCstrndup-call-memcpy-pre-4-goal5 where

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

record Exists (P : Int → Set) : Set where
  constructor witness
  field
    value    : Int
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

zeroZ oneZ uint32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
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

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

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

Goal5 :
  Uint32Projection →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal5 conversion region linked sconst =
  (i₁ : Int) →
  (source destination : Addr) →
  (i : Int) →
  (allocation : Int → Int) →
  (memory : Addr → Int) →
  let
    byte-count = toUint32 conversion (addInt oneZ i₁)
    source-start = shift source zeroZ
  in
  zeroAddr ≠ destination →
  byte-count ≠ zeroZ →
  zeroZ ≤Z i →
  region (base source) ≤Z zeroZ →
  linked allocation →
  sconst memory →
  IsUint32 i →
  IsUint32 i₁ →
  ValidRW allocation source-start i →
  (zeroZ <Z byte-count →
    ValidRW allocation (shift destination zeroZ) byte-count) →
  (((index : Int) →
      zeroZ ≤Z index →
      index <Z i →
      memory (shift source index) ≠ zeroZ) →
    i₁ ≡ i) →
  (Exists (λ index →
      (memory (shift source index) ≡ zeroZ) ∧
      (zeroZ ≤Z index) ∧
      (index <Z i)) →
    i₁ ≤Z i) →
  ValidRW allocation source-start i₁

strndup-call-memcpy-pre-4-goal5 : Set₁
strndup-call-memcpy-pre-4-goal5 =
  (conversion : Uint32Projection) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal5 conversion region linked sconst
