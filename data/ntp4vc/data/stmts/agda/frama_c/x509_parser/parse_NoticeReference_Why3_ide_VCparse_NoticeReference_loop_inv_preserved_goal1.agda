-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/x509_parser/parse_NoticeReference_Why3_ide_VCparse_NoticeReference_loop_inv_preserved_goal1:
-- under the stated nonzero, address, integer-range, region, linked-allocation,
-- and memory-validity assumptions, the remaining NoticeReference subrange is
-- valid for reading. This file contains no proof.

{-# OPTIONS --safe #-}

module parse_NoticeReference_Why3_ide_VCparse_NoticeReference_loop_inv_preserved_goal1 where

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

negateInt : Int → Int
negateInt (pos zero) = pos zero
negateInt (pos (suc n)) = negsuc n
negateInt (negsuc n) = pos (suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

zeroZ oneZ twoZ threeZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3

negativeInt32Lower uint16Maximum uint16Upper
  int32Maximum int32Upper : Int
negativeInt32Lower = negsuc 2147483647
uint16Maximum = pos 65535
uint16Upper = pos 65536
int32Maximum = pos 2147483647
int32Upper = pos 2147483648

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

Goal1 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal1 region linked =
  (a₁ a : Addr) →
  (i₄ i₅ i i₁ i₂ i₃ : Int) →
  (a₂ : Addr) →
  (i₆ : Int) →
  (allocation : Int → Int) →
  let
    x = base a₁
    x₁ = base a
    a₃ = shift a₁ i₄
    a₄ = shift a₁ (subtractInt (addInt i₄ i₅) i)
    x₃ = addInt i₄ i₅
    x₄ = subtractInt i₁ i₂
  in
  i ≠ zeroZ →
  i₁ ≠ zeroZ →
  i₃ ≠ zeroZ →
  i₅ ≠ zeroZ →
  zeroAddr ≠ a₁ →
  zeroAddr ≠ a₂ →
  x ≠ x₁ →
  a₃ ≠ zeroAddr →
  a₄ ≠ zeroAddr →
  zeroZ ≤Z i →
  i₆ ≤Z i →
  zeroZ ≤Z i₁ →
  i₂ ≤Z i₁ →
  zeroZ ≤Z i₃ →
  i₄ ≤Z i₃ →
  i₅ ≤Z i₃ →
  zeroZ ≤Z i₅ →
  zeroZ ≤Z i₆ →
  x₃ ≤Z i₃ →
  zeroZ ≤Z x₃ →
  region x₁ ≤Z zeroZ →
  region x ≤Z zeroZ →
  negativeInt32Lower ≤Z i →
  negativeInt32Lower ≤Z i₆ →
  twoZ ≤Z i₄ →
  threeZ ≤Z i₂ →
  i ≤Z uint16Maximum →
  i₆ ≤Z uint16Maximum →
  i ≤Z int32Maximum →
  i₆ ≤Z int32Maximum →
  negativeInt32Lower ≤Z x₃ →
  x₃ ≤Z uint16Maximum →
  x₃ ≤Z int32Maximum →
  addInt twoZ i₆ ≤Z i →
  i₁ ≤Z addInt uint16Maximum i₂ →
  i₁ ≤Z addInt int32Maximum i₂ →
  i₂ ≤Z addInt int32Upper i₁ →
  linked allocation →
  IsUint16 i →
  IsUint16 i₁ →
  IsUint16 i₂ →
  IsUint16 i₃ →
  IsUint16 i₄ →
  IsUint16 i₅ →
  IsUint16 i₆ →
  ValidRW allocation a oneZ →
  IsUint16 (subtractInt i i₆) →
  IsUint16 x₄ →
  IsUint16 (subtractInt i₅ i) →
  ValidRD allocation (shift a₂ zeroZ) i₁ →
  (zeroZ <Z i₃ →
    ValidRD allocation (shift a₁ zeroZ) i₃) →
  (zeroZ <Z i₅ →
    ValidRD allocation a₃ i₅) →
  (zeroZ <Z i →
    ValidRD allocation a₄ i) →
  ValidRD allocation (shift a₂ i₂) x₄

parse-NoticeReference-loop-inv-preserved-goal1 : Set₁
parse-NoticeReference-loop-inv-preserved-goal1 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal1 region linked
