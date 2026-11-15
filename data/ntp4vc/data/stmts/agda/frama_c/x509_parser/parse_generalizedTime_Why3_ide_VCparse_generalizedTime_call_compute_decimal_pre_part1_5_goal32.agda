-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/x509_parser/parse_generalizedTime_Why3_ide_VCparse_generalizedTime_call_compute_decimal_pre_part1_5_goal32:
-- under the stated address-distinctness, integer-range, region,
-- linked-allocation, digit-range, separation, and memory-validity assumptions,
-- the generalized-time character at offset fourteen is at least ASCII 48.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module parse-generalizedTime-Why3-ide-VCparse-generalizedTime-call-compute-decimal-pre-part1-5-goal32 where

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

zeroZ oneZ twoZ threeZ fourZ fiveZ sixZ sevenZ eightZ nineZ tenZ
  elevenZ twelveZ thirteenZ fourteenZ fifteenZ sixteenZ seventeenZ
  twentyFourZ fortyEightZ fiftySevenZ ninetyZ ninetyNineZ
  nineThousandNineHundredNinetyNineZ uint8Upper uint16Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3
fourZ = pos 4
fiveZ = pos 5
sixZ = pos 6
sevenZ = pos 7
eightZ = pos 8
nineZ = pos 9
tenZ = pos 10
elevenZ = pos 11
twelveZ = pos 12
thirteenZ = pos 13
fourteenZ = pos 14
fifteenZ = pos 15
sixteenZ = pos 16
seventeenZ = pos 17
twentyFourZ = pos 24
fortyEightZ = pos 48
fiftySevenZ = pos 57
ninetyZ = pos 90
ninetyNineZ = pos 99
nineThousandNineHundredNinetyNineZ = pos 9999
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

Goal32 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal32 region linked =
  (a₇ : Addr) →
  (integerMemory : Addr → Int) →
  (a₁ a a₂ a₃ a₄ a₅ a₆ : Addr) →
  (i i₂ i₃ i₄ i₅ i₆ i₁ : Int) →
  (allocation : Int → Int) →
  let
    a₈ = shift a₇ zeroZ
    a₉ = shift a₇ oneZ
    a₁₀ = shift a₇ sixteenZ
    a₁₁ = shift a₇ twoZ
    x = integerMemory a₁₁
    a₁₂ = shift a₇ threeZ
    x₁ = integerMemory a₁₂
    a₁₃ = shift a₇ fourZ
    x₂ = integerMemory a₁₃
    a₁₄ = shift a₇ fiveZ
    x₃ = integerMemory a₁₄
    a₁₅ = shift a₇ sixZ
    x₄ = integerMemory a₁₅
    a₁₆ = shift a₇ sevenZ
    x₅ = integerMemory a₁₆
    a₁₇ = shift a₇ eightZ
    x₆ = integerMemory a₁₇
    a₁₈ = shift a₇ nineZ
    x₇ = integerMemory a₁₈
    a₁₉ = shift a₇ tenZ
    x₈ = integerMemory a₁₉
    a₂₀ = shift a₇ elevenZ
    x₉ = integerMemory a₂₀
    a₂₁ = shift a₇ twelveZ
    x₁₀ = integerMemory a₂₁
    a₂₂ = shift a₇ thirteenZ
    x₁₁ = integerMemory a₂₂
    a₂₃ = shift a₇ fourteenZ
    x₁₂ = integerMemory a₂₃
    a₂₄ = shift a₇ fifteenZ
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
  zeroZ ≤Z i₂ →
  zeroZ ≤Z i₃ →
  zeroZ ≤Z i₄ →
  zeroZ ≤Z i₅ →
  zeroZ ≤Z i₆ →
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
  i₃ ≤Z ninetyNineZ →
  i₄ ≤Z ninetyNineZ →
  i₅ ≤Z ninetyNineZ →
  i₆ ≤Z ninetyNineZ →
  i₂ ≤Z nineThousandNineHundredNinetyNineZ →
  fortyEightZ ≤Z x →
  fortyEightZ ≤Z x₁ →
  fortyEightZ ≤Z x₂ →
  fortyEightZ ≤Z x₃ →
  fortyEightZ ≤Z x₄ →
  fortyEightZ ≤Z x₅ →
  fortyEightZ ≤Z x₆ →
  fortyEightZ ≤Z x₇ →
  fortyEightZ ≤Z x₈ →
  fortyEightZ ≤Z x₉ →
  fortyEightZ ≤Z x₁₀ →
  fortyEightZ ≤Z x₁₁ →
  x ≤Z fiftySevenZ →
  x₁ ≤Z fiftySevenZ →
  x₂ ≤Z fiftySevenZ →
  x₃ ≤Z fiftySevenZ →
  x₄ ≤Z fiftySevenZ →
  x₅ ≤Z fiftySevenZ →
  x₆ ≤Z fiftySevenZ →
  x₇ ≤Z fiftySevenZ →
  x₈ ≤Z fiftySevenZ →
  x₉ ≤Z fiftySevenZ →
  x₁₀ ≤Z fiftySevenZ →
  x₁₁ ≤Z fiftySevenZ →
  linked allocation →
  IsUint8 i₁ →
  IsUint8 i₃ →
  IsUint8 i₄ →
  IsUint8 i₅ →
  IsUint8 i₆ →
  IsUint16 i →
  IsUint16 i₂ →
  ValidRW allocation a oneZ →
  ValidRW allocation a₁ oneZ →
  ValidRW allocation a₂ oneZ →
  ValidRW allocation a₃ oneZ →
  ValidRW allocation a₄ oneZ →
  ValidRW allocation a₅ oneZ →
  ValidRW allocation a₆ oneZ →
  IsUint8 x →
  IsUint8 x₁ →
  IsUint8 x₂ →
  IsUint8 x₃ →
  IsUint8 x₄ →
  IsUint8 x₅ →
  IsUint8 x₆ →
  IsUint8 x₇ →
  IsUint8 x₈ →
  IsUint8 x₉ →
  IsUint8 x₁₀ →
  IsUint8 x₁₁ →
  IsUint8 x₁₂ →
  IsUint8 (integerMemory a₂₄) →
  ValidRD allocation a₈ oneZ →
  ValidRD allocation a₉ oneZ →
  ValidRD allocation a₁₁ oneZ →
  ValidRD allocation a₁₂ oneZ →
  ValidRD allocation a₁₃ oneZ →
  ValidRD allocation a₁₄ oneZ →
  ValidRD allocation a₁₅ oneZ →
  ValidRD allocation a₁₆ oneZ →
  ValidRD allocation a₁₇ oneZ →
  ValidRD allocation a₁₈ oneZ →
  ValidRD allocation a₁₉ oneZ →
  ValidRD allocation a₂₀ oneZ →
  ValidRD allocation a₂₁ oneZ →
  ValidRD allocation a₂₂ oneZ →
  ValidRD allocation a₂₃ oneZ →
  ValidRD allocation a₂₄ oneZ →
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
  ((i₇ : Int) →
    let
      x₁₃ = integerMemory (shift a₇ (addInt twoZ i₇))
    in
    zeroZ ≤Z i₇ →
    i₇ <Z i₁ →
    (fortyEightZ ≤Z x₁₃) ∧
    (x₁₃ ≤Z fiftySevenZ)) →
  fortyEightZ ≤Z x₁₂

parse-generalizedTime-call-compute-decimal-pre-part1-5-goal32 : Set₁
parse-generalizedTime-call-compute-decimal-pre-part1-5-goal32 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal32 region linked
