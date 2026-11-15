-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/x509_parser/parse_generalizedTime_Why3_ide_VCparse_generalizedTime_call_compute_year_pre_3_part1_goal12:
-- under the stated address-distinctness, integer-range, region,
-- linked-allocation, digit-range, separation, and memory-validity assumptions,
-- the generalized-time character at offset four is at least ASCII 48.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module parse-generalizedTime-Why3-ide-VCparse-generalizedTime-call-compute-year-pre-3-part1-goal12 where

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

zeroZ oneZ twoZ threeZ fourZ fiveZ fourteenZ fifteenZ sixteenZ
  seventeenZ twentyFourZ fortyEightZ fiftySevenZ ninetyZ
  uint8Upper uint16Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3
fourZ = pos 4
fiveZ = pos 5
fourteenZ = pos 14
fifteenZ = pos 15
sixteenZ = pos 16
seventeenZ = pos 17
twentyFourZ = pos 24
fortyEightZ = pos 48
fiftySevenZ = pos 57
ninetyZ = pos 90
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

IsUint8 : Int → Set
IsUint8 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint8Upper)

IsUint16 : Int → Set
IsUint16 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint16Upper)

Goal12 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal12 region linked =
  (a₇ : Addr) →
  (integerMemory : Addr → Int) →
  (a₁ a a₂ a₃ a₄ a₅ a₆ : Addr) →
  (i i₁ : Int) →
  (allocation : Int → Int) →
  let
    a₈ = shift a₇ zeroZ
    a₉ = shift a₇ oneZ
    a₁₀ = shift a₇ sixteenZ
    a₁₁ = shift a₇ twoZ
    a₁₂ = shift a₇ threeZ
    a₁₃ = shift a₇ fourZ
    x = integerMemory a₁₃
    a₁₄ = shift a₇ fiveZ
  in
  a₁ ≠ a →
  a₂ ≠ a →
  a₂ ≠ a₁ →
  a₃ ≠ a →
  a₃ ≠ a₁ →
  a₃ ≠ a₂ →
  a₄ ≠ a →
  a₄ ≠ a₁ →
  a₄ ≠ a₂ →
  a₄ ≠ a₃ →
  a₅ ≠ a →
  a₅ ≠ a₁ →
  a₅ ≠ a₂ →
  a₅ ≠ a₃ →
  a₅ ≠ a₄ →
  a₆ ≠ a →
  a₆ ≠ a₁ →
  a₆ ≠ a₂ →
  a₆ ≠ a₃ →
  a₆ ≠ a₄ →
  a₆ ≠ a₅ →
  zeroAddr ≠ a₇ →
  integerMemory a₈ ≡ twentyFourZ →
  integerMemory a₉ ≡ fifteenZ →
  integerMemory a₁₀ ≡ ninetyZ →
  zeroZ ≤Z i →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  region (base a₂) ≤Z zeroZ →
  region (base a₃) ≤Z zeroZ →
  region (base a₄) ≤Z zeroZ →
  region (base a₅) ≤Z zeroZ →
  region (base a₆) ≤Z zeroZ →
  region (base a₇) ≤Z zeroZ →
  fourteenZ ≤Z i₁ →
  seventeenZ ≤Z i →
  linked allocation →
  IsUint8 i₁ →
  IsUint16 i →
  ValidRW allocation a oneZ →
  ValidRW allocation a₁ oneZ →
  ValidRW allocation a₂ oneZ →
  ValidRW allocation a₃ oneZ →
  ValidRW allocation a₄ oneZ →
  ValidRW allocation a₅ oneZ →
  ValidRW allocation a₆ oneZ →
  IsUint8 (integerMemory a₁₁) →
  IsUint8 (integerMemory a₁₂) →
  IsUint8 x →
  IsUint8 (integerMemory a₁₄) →
  ValidRD allocation a₈ oneZ →
  ValidRD allocation a₉ oneZ →
  ValidRD allocation a₁₁ oneZ →
  ValidRD allocation a₁₂ oneZ →
  ValidRD allocation a₁₃ oneZ →
  ValidRD allocation a₁₄ oneZ →
  ValidRD allocation a₁₀ oneZ →
  Separated a oneZ a₈ i →
  Separated a₁ oneZ a₈ i →
  Separated a₂ oneZ a₈ i →
  Separated a₃ oneZ a₈ i →
  Separated a₄ oneZ a₈ i →
  Separated a₅ oneZ a₈ i →
  Separated a₆ oneZ a₈ i →
  ValidRD allocation (shift a₇ (addInt twoZ i₁)) oneZ →
  (zeroZ <Z i →
    ValidRD allocation a₈ i) →
  ((i₂ : Int) →
    let
      x₁ = integerMemory (shift a₇ (addInt twoZ i₂))
    in
    zeroZ ≤Z i₂ →
    i₂ <Z i₁ →
    (fortyEightZ ≤Z x₁) ∧
    (x₁ ≤Z fiftySevenZ)) →
  fortyEightZ ≤Z x

parse-generalizedTime-call-compute-year-pre-3-part1-goal12 : Set₁
parse-generalizedTime-call-compute-year-pre-3-part1-goal12 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal12 region linked
