-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/x509_parser/parse_UTCTime_Why3_ide_VCparse_UTCTime_call_compute_decimal_pre_part1_3_goal17:
-- under the stated address-distinctness, integer-range, region,
-- linked-allocation, digit-range, separation, and memory-validity assumptions,
-- the UTC-time character at offset six is at least ASCII 48. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module parse-UTCTime-Why3-ide-VCparse-UTCTime-call-compute-decimal-pre-part1-3-goal17 where

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

zeroZ oneZ twoZ threeZ fourZ fiveZ sixZ sevenZ twelveZ thirteenZ
  fourteenZ fifteenZ twentyThreeZ fortyEightZ fiftyZ fiftySevenZ ninetyZ
  ninetyNineZ uint8Upper uint16Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3
fourZ = pos 4
fiveZ = pos 5
sixZ = pos 6
sevenZ = pos 7
twelveZ = pos 12
thirteenZ = pos 13
fourteenZ = pos 14
fifteenZ = pos 15
twentyThreeZ = pos 23
fortyEightZ = pos 48
fiftyZ = pos 50
fiftySevenZ = pos 57
ninetyZ = pos 90
ninetyNineZ = pos 99
uint8Upper = pos 256
uint16Upper = pos 65536

negative1900 upper63635 upper2147481747 : Int
negative1900 = negsuc 1899
upper63635 = pos 63635
upper2147481747 = pos 2147481747

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

Goal17 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal17 region linked =
  (a₇ : Addr) →
  (integerMemory : Addr → Int) →
  (a₁ a a₂ a₃ a₄ a₅ a₆ : Addr) →
  (i i₁ i₃ i₂ : Int) →
  (allocation : Int → Int) →
  let
    a₈ = shift a₇ zeroZ
    a₉ = shift a₇ oneZ
    a₁₀ = shift a₇ fourteenZ
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
  integerMemory a₈ ≡ twentyThreeZ →
  integerMemory a₉ ≡ thirteenZ →
  integerMemory a₁₀ ≡ ninetyZ →
  zeroZ ≤Z i →
  zeroZ ≤Z i₁ →
  zeroZ ≤Z i₃ →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  region (base a₂) ≤Z zeroZ →
  region (base a₃) ≤Z zeroZ →
  region (base a₄) ≤Z zeroZ →
  region (base a₅) ≤Z zeroZ →
  region (base a₆) ≤Z zeroZ →
  region (base a₇) ≤Z zeroZ →
  negative1900 ≤Z i →
  twelveZ ≤Z i₂ →
  fifteenZ ≤Z i₁ →
  fiftyZ ≤Z i →
  i ≤Z ninetyNineZ →
  i₃ ≤Z ninetyNineZ →
  i ≤Z upper63635 →
  i ≤Z upper2147481747 →
  fortyEightZ ≤Z x →
  fortyEightZ ≤Z x₁ →
  fortyEightZ ≤Z x₂ →
  fortyEightZ ≤Z x₃ →
  x ≤Z fiftySevenZ →
  x₁ ≤Z fiftySevenZ →
  x₂ ≤Z fiftySevenZ →
  x₃ ≤Z fiftySevenZ →
  linked allocation →
  IsUint8 i →
  IsUint8 i₂ →
  IsUint8 i₃ →
  IsUint16 i →
  IsUint16 i₁ →
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
  IsUint8 (integerMemory a₁₆) →
  ValidRD allocation a₈ oneZ →
  ValidRD allocation a₉ oneZ →
  ValidRD allocation a₁₁ oneZ →
  ValidRD allocation a₁₂ oneZ →
  ValidRD allocation a₁₃ oneZ →
  ValidRD allocation a₁₄ oneZ →
  ValidRD allocation a₁₅ oneZ →
  ValidRD allocation a₁₆ oneZ →
  ValidRD allocation a₁₀ oneZ →
  Separated a oneZ a₈ i₁ →
  Separated a₁ oneZ a₈ i₁ →
  Separated a₂ oneZ a₈ i₁ →
  Separated a₃ oneZ a₈ i₁ →
  Separated a₄ oneZ a₈ i₁ →
  Separated a₅ oneZ a₈ i₁ →
  Separated a₆ oneZ a₈ i₁ →
  ValidRD allocation (shift a₇ (addInt twoZ i₂)) oneZ →
  (zeroZ <Z i₁ →
    ValidRD allocation a₈ i₁) →
  ((i₄ : Int) →
    let
      x₅ = integerMemory (shift a₇ (addInt twoZ i₄))
    in
    zeroZ ≤Z i₄ →
    i₄ <Z i₂ →
    (fortyEightZ ≤Z x₅) ∧
    (x₅ ≤Z fiftySevenZ)) →
  fortyEightZ ≤Z x₄

parse-UTCTime-call-compute-decimal-pre-part1-3-goal17 : Set₁
parse-UTCTime-call-compute-decimal-pre-part1-3-goal17 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal17 region linked
