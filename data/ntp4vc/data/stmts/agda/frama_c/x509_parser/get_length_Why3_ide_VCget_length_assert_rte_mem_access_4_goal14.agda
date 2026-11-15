-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/x509_parser/get_length_Why3_ide_VCget_length_assert_rte_mem_access_4_goal14:
-- under the stated address, bit-pattern, integer-range, region,
-- linked-allocation, and memory-validity assumptions, the byte at offset two
-- from the input address is valid for a one-unit read. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module get-length-Why3-ide-VCget-length-assert-rte-mem-access-4-goal14 where

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

zeroZ oneZ twoZ threeZ value128 lowSevenModulus byteModulus
  uint8Upper uint16Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3
value128 = pos 128
lowSevenModulus = pos 128
byteModulus = pos 256
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

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

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

-- For mathematical integers, 127 bitwise-and x equals 2 exactly when
-- x is congruent to 2 modulo 128.
LowSevenBitsEqual2 : Int → Set
LowSevenBitsEqual2 x =
  Exists Int λ quotient →
    x ≡ addInt
      (multiplyInt quotient lowSevenModulus)
      twoZ

-- Bit seven is set exactly when the residue modulo 256 lies in [128, 256).
BitSevenSet : Int → Set
BitSevenSet x =
  Exists Int λ quotient →
    Exists Int λ remainder →
      (x ≡ addInt
        (multiplyInt quotient byteModulus)
        remainder) ∧
      (value128 ≤Z remainder) ∧
      (remainder <Z byteModulus)

Goal14 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal14 region linked =
  (a₁ a a₂ : Addr) →
  (integer-memory : Addr → Int) →
  (i : Int) →
  (allocation : Int → Int) →
  let
    x = base a₁
    x₁ = base a
    x₂ = base a₂
    a₃ = shift a₁ zeroZ
    x₃ = integer-memory a₃
  in
  i ≠ zeroZ →
  a₂ ≠ a →
  zeroAddr ≠ a₁ →
  x ≠ x₁ →
  x₂ ≠ x →
  x₃ ≠ value128 →
  LowSevenBitsEqual2 x₃ →
  zeroZ ≤Z i →
  region x₁ ≤Z zeroZ →
  region x ≤Z zeroZ →
  region x₂ ≤Z zeroZ →
  threeZ ≤Z i →
  linked allocation →
  IsUint16 i →
  ValidRW allocation a oneZ →
  ValidRW allocation a₂ oneZ →
  IsUint8 x₃ →
  BitSevenSet x₃ →
  ValidRD allocation a₃ oneZ →
  (zeroZ <Z i →
    ValidRD allocation a₃ i) →
  ValidRD allocation (shift a₁ twoZ) oneZ

get-length-assert-rte-mem-access-4-goal14 : Set₁
get-length-assert-rte-mem-access-4-goal14 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal14 region linked
