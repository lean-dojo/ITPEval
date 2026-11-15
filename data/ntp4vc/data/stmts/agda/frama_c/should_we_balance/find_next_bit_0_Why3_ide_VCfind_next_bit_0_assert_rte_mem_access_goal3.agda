-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/should_we_balance/find_next_bit_0_Why3_ide_VCfind_next_bit_0_assert_rte_mem_access_goal3:
-- under the stated index bounds, allocation linkage, unsigned-integer
-- ranges, byte-content condition, readable range, and preceding-zero
-- condition, the address shifted by i₂ is readable for one byte.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module find-next-bit-0-Why3-ide-VCfind-next-bit-0-assert-rte-mem-access-goal3 where

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

uint8Upper uint32Upper signed32Maximum : Int
uint8Upper = pos 256
uint32Upper = pos 4294967296
signed32Maximum = pos 2147483647

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

IsUint8 : Int → Set
IsUint8 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint8Upper)

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

Goal3 :
  Int →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal3 lSize region linked =
  (a : Addr) →
  (i₂ i i₁ : Int) →
  (allocation : Int → Int) →
  (byteMemory : Addr → Int) →
  let a₁ = shift a i₂
  in
  i₂ <Z i →
  i₁ ≤Z i₂ →
  i ≤Z lSize →
  region (base a) ≤Z zeroZ →
  linked allocation →
  IsUint32 i →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint8 (byteMemory a₁) →
  ValidRD allocation (shift a zeroZ) i →
  ((i₃ : Int) →
    i₁ ≤Z i₃ →
    i₃ <Z i₂ →
    byteMemory (shift a i₃) ≡ zeroZ) →
  ValidRD allocation a₁ oneZ

find-next-bit-0-assert-rte-mem-access-goal3 : Set₁
find-next-bit-0-assert-rte-mem-access-goal3 =
  (lSize : Int) →
  ((zeroZ <Z lSize) ∧ (lSize ≤Z signed32Maximum)) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal3 lSize region linked
