-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/linked_n_merge_segment_Why3_ide_VClinked_n_merge_segment_loop_inv_4_established_goal11:
-- establishment of the linked-list suffix invariant beginning at the pointer
-- reached after the merged segment, under the stated integer, region,
-- framing, linkedness, memory-validity, and linked-segment assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module LinkedNMergeSegmentLoopInv4EstablishedGoal11 where

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

zeroZ oneZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
fourZ = pos (suc (suc (suc (suc zero))))

maximumArrayIndex signed32Lower signed32Upper : Int
maximumArrayIndex = pos 2147483646
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

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

data PLinkedN :
  (Int → Int) →
  (Addr → Addr) →
  Addr →
  Addr →
  Int →
  Int →
  Addr →
  Set where

  linked-bound :
    (index : Int) →
    (allocation : Int → Int) →
    (pointer-memory : Addr → Addr) →
    (bound array : Addr) →
    zeroZ ≤Z index →
    index ≤Z maximumArrayIndex →
    PLinkedN
      allocation pointer-memory bound array index zeroZ bound

  linked-cons :
    (index n : Int) →
    (pointer-memory : Addr → Addr) →
    (array root : Addr) →
    (allocation : Int → Int) →
    (bound : Addr) →
    pointer-memory (shift array index) ≡ root →
    zeroZ <Z n →
    zeroZ ≤Z index →
    zeroZ ≤Z addInt index n →
    addInt index n ≤Z maximumArrayIndex →
    ValidRW allocation root fourZ →
    PLinkedN
      allocation
      pointer-memory
      (pointer-memory (shift root zeroZ))
      array
      (addInt oneZ index)
      (subtractInt n oneZ)
      bound →
    PLinkedN
      allocation pointer-memory root array index n bound

module VC
  (region : Int → Int)
  (linked : (Int → Int) → Set) where

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (base (pointer-memory p)) ≤Z zeroZ

  goal11 : Set
  goal11 =
    (i1 i2 i : Int) →
    (a a1 a2 a3 : Addr) →
    (pointer-memory : Addr → Addr) →
    (allocation : Int → Int) →
    let x = addInt i1 i2
    in
    i2 ≠ zeroZ →
    zeroZ ≤Z i →
    zeroZ ≤Z i2 →
    region (base a) ≤Z zeroZ →
    region (base a1) ≤Z zeroZ →
    region (base a2) ≤Z zeroZ →
    region (base a3) ≤Z zeroZ →
    Framed pointer-memory →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    IsSint32 i2 →
    ValidRW allocation (shift a3 zeroZ) maximumArrayIndex →
    PLinkedN allocation pointer-memory a a3 i1 i2 a2 →
    PLinkedN allocation pointer-memory a2 a3 x i a1 →
    PLinkedN
      allocation
      pointer-memory
      (pointer-memory
        (shift
          (pointer-memory
            (shift a3 (subtractInt x oneZ)))
          zeroZ))
      a3
      x
      i
      a1

linked-n-merge-segment-loop-invariant-4-established-goal11 : Set₁
linked-n-merge-segment-loop-invariant-4-established-goal11 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  VC.goal11 region linked
