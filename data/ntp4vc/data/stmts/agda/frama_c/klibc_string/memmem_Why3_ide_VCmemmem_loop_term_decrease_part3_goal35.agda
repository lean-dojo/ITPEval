-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/klibc_string/memmem_Why3_ide_VCmemmem_loop_term_decrease_part3_goal35:
-- decrease of the memmem loop variant, concluding that the current offset is
-- below its unsigned-32-bit successor under the stated integer, byte,
-- memory-validity, separation, linkedness, and mismatch assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module memmem-Why3-ide-VCmemmem-loop-term-decrease-part3-goal35 where

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

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

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

zeroZ oneZ twoZ threeZ uint8Upper uint32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3
uint8Upper = pos 256
uint32Upper = pos 4294967296

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
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

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

record CIntegerProjection : Set where
  field
    toUint32 : Int → Int

    toUint32-in-range :
      (x : Int) →
      IsUint32 (toUint32 x)

    toUint32-identity :
      (x : Int) →
      IsUint32 x →
      toUint32 x ≡ x

open CIntegerProjection

Goal35 :
  CIntegerProjection →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal35 projection region linked =
  (a₈ a₉ : Addr) →
  (scalarMemory : Addr → Int) →
  (a₁ a : Addr) →
  (i₂ : Int) →
  (a₆ : Addr) →
  (i₁ : Int) →
  (a₇ : Addr) →
  (i : Int) →
  (allocation : Int → Int) →
  (a₅ a₄ a₃ a₂ : Addr) →
  let
    x = base a₈
    x₁ = base a₉
    x₂ = scalarMemory (shift a₁ zeroZ)
    x₃ = scalarMemory (shift a i₂)
    x₄ = scalarMemory (shift a₁ oneZ)
    x₅ = toUint32 projection (addInt oneZ i₂)
    x₆ = scalarMemory (shift a x₅)
    a₁₀ = shift a₈ zeroZ
    a₁₁ = shift a₉ zeroZ
    a₁₂ = shift a₆ zeroZ
    x₇ = toUint32 projection (subtractInt i₁ twoZ)
    a₁₃ = shift a₇ zeroZ
  in
  i ≠ zeroZ →
  i₁ ≠ zeroZ →
  i₁ ≠ oneZ →
  x ≡ base a₁ →
  x₁ ≡ base a →
  x₂ ≠ x₃ →
  x₄ ≡ x₂ →
  x₆ ≡ x₄ →
  zeroZ ≤Z i →
  i₁ ≤Z i →
  zeroZ ≤Z i₁ →
  zeroZ ≤Z i₂ →
  region x ≤Z zeroZ →
  region x₁ ≤Z zeroZ →
  i₂ ≤Z toUint32 projection (subtractInt i i₁) →
  addInt i₁ i₂ ≤Z addInt twoZ i →
  linked allocation →
  IsUint32 i →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint8 x₃ →
  IsUint8 x₂ →
  IsUint8 x₄ →
  ValidRW allocation a₁₀ i₁ →
  ValidRW allocation a₁₁ i →
  Separated a₁₁ i a₁₀ i₁ →
  ValidRW allocation a₁₂ x₇ →
  ValidRW allocation a₁₃ x₇ →
  Separated a₁₃ x₇ a₁₂ x₇ →
  IsUint8 x₆ →
  (zeroZ <Z x₇ →
    Not
      (Exists Int
        (λ i₃ →
          (scalarMemory (shift a₅ i₃) ≠ scalarMemory (shift a₄ i₃)) ∧
          (zeroZ ≤Z i₃) ∧
          (i₃ <Z x₇)))) →
  ((i₃ : Int) →
    zeroZ ≤Z i₃ →
    i₃ <Z i₂ →
    Exists Int
      (λ i₄ →
        zeroZ ≤Z i₄ →
        addInt threeZ i₄ ≤Z i₁ →
        scalarMemory (shift a₃ (addInt (addInt twoZ i₄) i₃))
          ≠ scalarMemory (shift a₂ (addInt twoZ i₄)))) →
  i₂ <Z x₅

memmem-loop-term-decrease-part3-goal35 : Set₁
memmem-loop-term-decrease-part3-goal35 =
  (projection : CIntegerProjection) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal35 projection region linked
