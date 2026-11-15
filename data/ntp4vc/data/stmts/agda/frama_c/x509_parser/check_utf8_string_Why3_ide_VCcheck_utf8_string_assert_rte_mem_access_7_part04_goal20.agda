-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/x509_parser/check_utf8_string_Why3_ide_VCcheck_utf8_string_assert_rte_mem_access_7_part04_goal20:
-- under the stated nonzero, address, byte-range, integer-range, region,
-- linked-allocation, and memory-read assumptions, the byte following the
-- current UTF-8 position is valid for a one-unit read. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module check-utf8-string-Why3-ide-VCcheck-utf8-string-assert-rte-mem-access-7-part04-goal20 where

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

zeroZ oneZ fourZ lower128 lower194 lower224 lower240 upper244
  uint8Upper uint16Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
fourZ = pos 4
lower128 = pos 128
lower194 = pos 194
lower224 = pos 224
lower240 = pos 240
upper244 = pos 244
uint8Upper = pos 256
uint16Upper = pos 65536

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

IsUint16 : Int → Set
IsUint16 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint16Upper)

Goal20 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal20 region linked =
  (a₁ : Addr) →
  (integer-memory : Addr → Int) →
  (i i₁ : Int) →
  (a : Addr) →
  (allocation : Int → Int) →
  let
    a₂ = shift a₁ zeroZ
    x = integer-memory a₂
  in
  i ≠ zeroZ →
  i₁ ≠ zeroZ →
  zeroAddr ≠ a →
  x ≠ lower240 →
  x ≠ upper244 →
  zeroZ ≤Z i₁ →
  region (base a) ≤Z zeroZ →
  fourZ ≤Z i →
  lower128 ≤Z x →
  lower194 ≤Z x →
  lower224 ≤Z x →
  lower240 ≤Z x →
  x ≤Z upper244 →
  linked allocation →
  IsUint16 i →
  IsUint16 i₁ →
  IsUint8 x →
  ValidRD allocation a₂ oneZ →
  ValidRD allocation a₂ i →
  (zeroZ <Z i₁ →
    ValidRD allocation (shift a zeroZ) i₁) →
  ValidRD allocation (shift a₁ oneZ) oneZ

check-utf8-string-assert-rte-mem-access-7-part04-goal20 : Set₁
check-utf8-string-assert-rte-mem-access-7-part04-goal20 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal20 region linked
