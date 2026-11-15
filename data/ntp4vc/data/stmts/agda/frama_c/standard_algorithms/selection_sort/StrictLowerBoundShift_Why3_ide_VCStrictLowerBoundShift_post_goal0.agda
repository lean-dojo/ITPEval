-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/selection_sort/StrictLowerBoundShift_Why3_ide_VCStrictLowerBoundShift_post_goal0:
-- under the stated integer-range and memory-region assumptions, a strict
-- integer lower bound on a shifted array interval is preserved when the base
-- and interval endpoints are shifted together. This file contains no proof.

{-# OPTIONS --safe #-}

module StrictLowerBoundShift_Why3_ide_VCStrictLowerBoundShift_post_goal0 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

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

zeroZ uint32Maximum uint32Upper signed32Lower signed32Upper : Int
zeroZ = pos zero
uint32Maximum = pos 4294967295
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

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

PStrictLowerBound :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PStrictLowerBound integer-memory a lower upper value =
  (index : Int) →
  lower ≤Z index →
  index <Z upper →
  value <Z integer-memory (shift a index)

Goal0 : (Int → Int) → Set
Goal0 region =
  (i1 : Int) →
  (i3 : Int) →
  (a : Addr) →
  (i2 : Int) →
  (i : Int) →
  (integer-memory : Addr → Int) →
  let x = addInt i1 i3
  in
  region (base a) ≤Z zeroZ →
  x ≤Z uint32Maximum →
  IsUint32 i1 →
  IsUint32 i2 →
  IsUint32 i3 →
  IsSint32 i →
  PStrictLowerBound integer-memory (shift a i3) i2 i1 i →
  PStrictLowerBound integer-memory a (addInt i2 i3) x i

strict-lower-bound-shift-post-goal0 : Set
strict-lower-bound-shift-post-goal0 =
  (region : Int → Int) →
  Goal0 region
