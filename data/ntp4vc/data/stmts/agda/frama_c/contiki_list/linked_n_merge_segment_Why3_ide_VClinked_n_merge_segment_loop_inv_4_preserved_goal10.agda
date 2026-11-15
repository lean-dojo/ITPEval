-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/linked_n_merge_segment_Why3_ide_VClinked_n_merge_segment_loop_inv_4_preserved_goal10:
-- preservation of the linked-list suffix invariant after extending a merged
-- segment by one node, under the stated integer, region, framing, linkedness,
-- memory-validity, and linked-segment assumptions. This file contains no proof.

{-# OPTIONS --safe #-}

module LinkedNMergeSegmentLoopInv4PreservedGoal10 where

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

zeroZ oneZ twoZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
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

  goal10 : Set
  goal10 =
    (i2 i3 : Int) →
    (pointer-memory : Addr → Addr) →
    (array : Addr) →
    (i i1 : Int) →
    (root bound intermediate-bound : Addr) →
    (allocation : Int → Int) →
    let
      x = subtractInt (addInt i2 i3) oneZ
      current-bound =
        pointer-memory
          (shift
            (pointer-memory (shift array x))
            zeroZ)
      preceding-root =
        pointer-memory
          (shift
            (pointer-memory
              (shift array (subtractInt (addInt i2 i3) twoZ)))
            zeroZ)
    in
    i ≠ zeroZ →
    zeroZ <Z i3 →
    zeroZ ≤Z i →
    i3 ≤Z i →
    zeroZ ≤Z i1 →
    region (base root) ≤Z zeroZ →
    region (base bound) ≤Z zeroZ →
    region (base intermediate-bound) ≤Z zeroZ →
    region (base array) ≤Z zeroZ →
    twoZ ≤Z i3 →
    Framed pointer-memory →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    IsSint32 i2 →
    IsSint32 i3 →
    IsSint32 (subtractInt i3 oneZ) →
    ValidRW allocation (shift array zeroZ) maximumArrayIndex →
    PLinkedN allocation pointer-memory root array i2 i intermediate-bound →
    PLinkedN
      allocation
      pointer-memory
      intermediate-bound
      array
      (addInt i i2)
      i1
      bound →
    PLinkedN allocation pointer-memory root array i2 i3 current-bound →
    PLinkedN
      allocation
      pointer-memory
      current-bound
      array
      (addInt i2 i3)
      (subtractInt (addInt i i1) i3)
      bound →
    PLinkedN
      allocation
      pointer-memory
      preceding-root
      array
      x
      (subtractInt (addInt (addInt oneZ i) i1) i3)
      bound

linked-n-merge-segment-loop-invariant-4-preserved-goal10 : Set₁
linked-n-merge-segment-loop-invariant-4-preserved-goal10 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  VC.goal10 region linked
