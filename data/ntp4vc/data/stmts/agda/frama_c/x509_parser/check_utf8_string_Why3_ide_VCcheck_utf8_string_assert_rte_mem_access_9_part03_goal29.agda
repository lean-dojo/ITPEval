-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/x509_parser/check_utf8_string_Why3_ide_VCcheck_utf8_string_assert_rte_mem_access_9_part03_goal29:
-- under the stated nonzero, address, UTF-8 byte-pattern, integer-range,
-- region, linked-allocation, and memory-read assumptions, the fourth byte
-- from the current UTF-8 position is valid for a one-unit read. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module check-utf8-string-Why3-ide-VCcheck-utf8-string-assert-rte-mem-access-9-part03-goal29 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

zeroZ oneZ twoZ threeZ fourZ lower128 upper143 maskUpper
  byteModulus value244 uint8Upper uint16Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3
fourZ = pos 4
lower128 = pos 128
upper143 = pos 143
maskUpper = pos 192
byteModulus = pos 256
value244 = pos 244
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

-- For mathematical integers, 192 bitwise-and x equals 128 exactly when
-- the residue of x modulo 256 lies in the half-open interval [128, 192).
Mask192Equals128 : Int → Set
Mask192Equals128 x =
  Exists Int λ quotient →
    Exists Int λ residue →
      (x ≡ addInt
        (multiplyInt quotient byteModulus)
        residue) ∧
      (lower128 ≤Z residue) ∧
      (residue <Z maskUpper)

Goal29 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal29 region linked =
  (a₁ : Addr) →
  (integer-memory : Addr → Int) →
  (i i₁ : Int) →
  (a : Addr) →
  (allocation : Int → Int) →
  let
    a₂ = shift a₁ zeroZ
    a₃ = shift a₁ oneZ
    x = integer-memory a₃
    a₄ = shift a₁ twoZ
    x₁ = integer-memory a₄
    a₅ = shift a₁ threeZ
  in
  i ≠ zeroZ →
  i₁ ≠ zeroZ →
  zeroAddr ≠ a →
  integer-memory a₂ ≡ value244 →
  Mask192Equals128 x →
  Mask192Equals128 x₁ →
  zeroZ ≤Z i₁ →
  region (base a) ≤Z zeroZ →
  fourZ ≤Z i →
  lower128 ≤Z x →
  x ≤Z upper143 →
  linked allocation →
  IsUint16 i →
  IsUint16 i₁ →
  IsUint8 x →
  IsUint8 x₁ →
  IsUint8 (integer-memory a₅) →
  ValidRD allocation a₂ oneZ →
  ValidRD allocation a₂ i →
  ValidRD allocation a₃ oneZ →
  ValidRD allocation a₄ oneZ →
  (zeroZ <Z i₁ →
    ValidRD allocation (shift a zeroZ) i₁) →
  ValidRD allocation a₅ oneZ

check-utf8-string-assert-rte-mem-access-9-part03-goal29 : Set₁
check-utf8-string-assert-rte-mem-access-9-part03-goal29 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal29 region linked
