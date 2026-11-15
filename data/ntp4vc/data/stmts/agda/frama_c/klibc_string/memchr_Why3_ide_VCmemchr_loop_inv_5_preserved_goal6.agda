-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/klibc_string/memchr_Why3_ide_VCmemchr_loop_inv_5_preserved_goal6:
-- preservation of the memchr loop invariant stating that the inspected byte
-- at the selected index differs from the searched signed byte, under the
-- stated bounds, memory, address-order, linkedness, and constancy assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module memchr-Why3-ide-VCmemchr-loop-inv-5-preserved-goal6 where

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

zeroZ oneZ signedByteLower signedByteUpper uint32Upper
  signed32Lower signed32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
signedByteLower = negsuc 127
signedByteUpper = pos 127
uint32Upper = pos 4294967296
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

AddrLE : Addr → Addr → Set
AddrLE p q = offset p ≤Z offset q

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

IsSint8 : Int → Set
IsSint8 x =
  (signedByteLower ≤Z x) ∧
  (x <Z pos 128)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

record CIntegerProjection : Set where
  field
    toSint8  : Int → Int
    toUint32 : Int → Int

    toSint8-in-range :
      (x : Int) →
      IsSint8 (toSint8 x)

    toUint32-in-range :
      (x : Int) →
      IsUint32 (toUint32 x)

    toSint8-identity :
      (x : Int) →
      IsSint8 x →
      toSint8 x ≡ x

    toUint32-identity :
      (x : Int) →
      IsUint32 x →
      toUint32 x ≡ x

open CIntegerProjection

Goal6 :
  CIntegerProjection →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal6 projection region linked sconst =
  (a : Addr) →
  (i₁ i : Int) →
  (t₁ : Addr → Int) →
  (i₃ i₂ : Int) →
  (allocation : Int → Int) →
  let
    a₁ = shift a (subtractInt i₁ i)
    x = t₁ a₁
    x₁ = toSint8 projection i₃
  in
  i ≠ zeroZ →
  x ≠ x₁ →
  zeroZ <Z i₁ →
  zeroZ ≤Z i →
  i ≤Z i₁ →
  zeroZ ≤Z i₂ →
  region (base a) ≤Z zeroZ →
  addInt i₂ (toUint32 projection (subtractInt i oneZ)) <Z i₁ →
  signedByteLower ≤Z i₃ →
  i₃ ≤Z signedByteUpper →
  linked allocation →
  sconst t₁ →
  IsUint32 i →
  IsUint32 i₁ →
  IsSint32 i₃ →
  ValidRW allocation (shift a zeroZ) i₁ →
  AddrLE a a₁ →
  AddrLE a₁ (shift a i₁) →
  IsSint8 x →
  ((i₄ : Int) →
    zeroZ ≤Z i₄ →
    addInt i₄ i <Z i₁ →
    t₁ (shift a i₄) ≠ x₁) →
  t₁ (shift a i₂) ≠ x₁

memchr-loop-inv-5-preserved-goal6 : Set₁
memchr-loop-inv-5-preserved-goal6 =
  (projection : CIntegerProjection) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal6 projection region linked sconst
