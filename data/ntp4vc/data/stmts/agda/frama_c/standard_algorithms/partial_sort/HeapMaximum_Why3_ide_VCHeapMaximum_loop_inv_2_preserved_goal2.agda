-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/partial_sort/HeapMaximum_Why3_ide_VCHeapMaximum_loop_inv_2_preserved_goal2:
-- under the stated unsigned-index bounds, region condition, heap invariant,
-- and prefix upper-bound invariant, the value at index i₂ is at most the
-- value at the root of the heap. This file contains no proof.

{-# OPTIONS --safe #-}

module heap-maximum-Why3-ide-VCHeapMaximum-loop-inv-2-preserved-goal2 where

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

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

negativeNat : Nat → Int
negativeNat zero = pos zero
negativeNat (suc n) = negsuc n

cdivTwo : Int → Int
cdivTwo (pos n) = pos (halfNat n)
cdivTwo (negsuc n) = negativeNat (halfNat (suc n))

zeroZ oneZ minusOneZ uint32Upper uint32MaximumMinusOne : Int
zeroZ = pos zero
oneZ = pos (suc zero)
minusOneZ = negsuc zero
uint32Upper = pos 4294967296
uint32MaximumMinusOne = pos 4294967294

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

IsUint32 : Int → Set
IsUint32 value =
  (zeroZ ≤Z value) ∧
  (value <Z uint32Upper)

heapParent : Int → Int
heapParent index =
  cdivTwo (addInt index minusOneZ)

PIsHeap :
  (Addr → Int) →
  Addr →
  Int →
  Set
PIsHeap integer-memory a upper =
  (index : Int) →
  zeroZ <Z index →
  index <Z upper →
  integer-memory (shift a index)
    ≤Z
  integer-memory (shift a (heapParent index))

Goal2 : (Int → Int) → Set
Goal2 region =
  (integer-memory : Addr → Int) →
  (a : Addr) →
  (i i₁ i₂ : Int) →
  let root-value = integer-memory (shift a zeroZ)
  in
  zeroZ <Z i →
  i₁ ≤Z i →
  zeroZ ≤Z i₁ →
  i₁ <Z i →
  i₂ ≤Z i₁ →
  zeroZ ≤Z i₂ →
  region (base a) ≤Z zeroZ →
  i₁ ≤Z uint32MaximumMinusOne →
  IsUint32 i →
  IsUint32 i₁ →
  IsUint32 i₂ →
  PIsHeap integer-memory a i →
  IsUint32 (addInt oneZ i₁) →
  ((i₃ : Int) →
    zeroZ ≤Z i₃ →
    i₃ <Z i₁ →
    integer-memory (shift a i₃) ≤Z root-value) →
  integer-memory (shift a i₂) ≤Z root-value

heap-maximum-loop-inv-2-preserved-goal2 : Set
heap-maximum-loop-inv-2-preserved-goal2 =
  (region : Int → Int) →
  Goal2 region
