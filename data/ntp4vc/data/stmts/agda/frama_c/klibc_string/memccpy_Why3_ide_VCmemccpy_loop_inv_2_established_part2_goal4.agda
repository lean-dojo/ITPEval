-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_loop_inv_2_established_part2_goal4:
-- under the stated region, byte and 32-bit integer bounds, linkedness,
-- scalar constancy, writable-memory, and separation assumptions, the
-- destination address is ordered below its shift by the positive length.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module memccpy-Why3-ide-VCmemccpy-loop-inv-2-established-part2-goal4 where

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

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

zeroZ signedByteLower signedByteUpper uint32Upper
  signed32Lower signed32Upper : Int
zeroZ = pos zero
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

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

Goal4 :
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal4 region linked sconst =
  (a a₁ : Addr) →
  (i i₁ : Int) →
  (allocation : Int → Int) →
  (scalarMemory : Addr → Int) →
  let
    source = shift a zeroZ
    destination = shift a₁ zeroZ
  in
  zeroZ <Z i →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  signedByteLower ≤Z i₁ →
  i₁ ≤Z signedByteUpper →
  linked allocation →
  sconst scalarMemory →
  IsUint32 i →
  IsSint32 i₁ →
  ValidRW allocation source i →
  ValidRW allocation destination i →
  Separated source i destination i →
  AddrLE a₁ (shift a₁ i)

memccpy-loop-inv-2-established-part2-goal4 : Set₁
memccpy-loop-inv-2-established-part2-goal4 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal4 region linked sconst
