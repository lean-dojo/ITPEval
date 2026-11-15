-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/x509_parser/_parse_arc_Why3_ide_VC_parse_arc_assert_rte_mem_access_part1_goal5:
-- under the stated address-separation, integer-range, region, linked-allocation,
-- bit-seven, and memory-validity assumptions, the next byte of the parsed arc
-- is readable. This file contains no proof.

{-# OPTIONS --safe #-}

module _parse_arc_Why3_ide_VC_parse_arc_assert_rte_mem_access_part1_goal5 where

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

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

powerOfTwo : Nat → Nat
powerOfTwo zero = suc zero
powerOfTwo (suc n) = 2 * powerOfTwo n

leftShift : Int → Int → Int
leftShift value amount =
  multiplyInt value (pos (powerOfTwo (intToNat amount)))

zeroZ oneZ threeZ fourZ fiveZ sevenZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
threeZ = pos 3
fourZ = pos 4
fiveZ = pos 5
sevenZ = pos 7

bitSevenLower uint16Upper bitSevenModulus uint32Maximum uint32Upper : Int
bitSevenLower = pos 128
uint16Upper = pos 65536
bitSevenModulus = pos 256
uint32Maximum = pos 4294967295
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

ValidRD : (Int → Int) → Addr → Int → Set
ValidRD allocation p n =
  zeroZ <Z n →
  (zeroZ ≠ base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

IsUint16 : Int → Set
IsUint16 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint16Upper)

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

CongruentModulo : Int → Int → Int → Set
CongruentModulo modulus x y =
  Exists Int λ multiple →
    x ≡ addInt y (multiplyInt multiple modulus)

record Uint32Projection : Set where
  field
    toUint32 : Int → Int

    toUint32-in-range :
      (x : Int) →
      IsUint32 (toUint32 x)

    toUint32-congruent :
      (x : Int) →
      CongruentModulo uint32Upper x (toUint32 x)

open Uint32Projection

BitSevenSet : Int → Set
BitSevenSet x =
  Exists Int λ quotient →
    Exists Int λ remainder →
      (x ≡ addInt
        (multiplyInt quotient bitSevenModulus)
        remainder) ∧
      (bitSevenLower ≤Z remainder) ∧
      (remainder <Z bitSevenModulus)

Goal5 :
  Uint32Projection →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal5 conversion region linked =
  (a₁ a a₂ : Addr) →
  (i₁ i i₂ : Int) →
  (allocation : Int → Int) →
  (integerMemory : Addr → Int) →
  let
    x = base a₁
    x₁ = base a
    x₂ = base a₂
  in
  i₁ ≠ zeroZ →
  a₂ ≠ a →
  zeroAddr ≠ a₁ →
  x ≠ x₁ →
  x₂ ≠ x →
  zeroZ ≤Z i →
  zeroZ ≤Z i₁ →
  region x₁ ≤Z zeroZ →
  region x ≤Z zeroZ →
  region x₂ ≤Z zeroZ →
  i₂ <Z leftShift
    oneZ
    (toUint32 conversion (multiplyInt sevenZ i)) →
  i ≤Z threeZ →
  i ≤Z fourZ →
  fiveZ ≤Z i₁ →
  leftShift i₂ sevenZ ≤Z uint32Maximum →
  linked allocation →
  IsUint16 i →
  IsUint16 i₁ →
  IsUint32 i₂ →
  ValidRW allocation a oneZ →
  ValidRW allocation a₂ oneZ →
  (zeroZ <Z i₁ →
    ValidRD allocation (shift a₁ zeroZ) i₁) →
  ((i₃ : Int) →
    zeroZ ≤Z i₃ →
    i₃ <Z i →
    BitSevenSet (integerMemory (shift a₁ i₃))) →
  ValidRD allocation (shift a₁ i) oneZ

parse-arc-assert-rte-mem-access-part1-goal5 : Set₁
parse-arc-assert-rte-mem-access-part1-goal5 =
  (conversion : Uint32Projection) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal5 conversion region linked
