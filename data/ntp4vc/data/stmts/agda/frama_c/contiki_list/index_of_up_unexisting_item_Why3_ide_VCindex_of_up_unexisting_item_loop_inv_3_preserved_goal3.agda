-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/index_of_up_unexisting_item_Why3_ide_VCindex_of_up_unexisting_item_loop_inv_3_preserved_goal3:
-- the index-of result remains the upper endpoint when the current lower
-- index advances by one, under the stated absence, ordering, signed-integer,
-- region, and framing assumptions. This file contains no proof.

{-# OPTIONS --safe #-}

module IndexOfUpUnexistingItemLoopInv3PreservedGoal3 where

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

zeroZ oneZ signed32Lower signed32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
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

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

record IndexOfTheory : Set where
  field
    lIndexOf :
      (Addr → Addr) →
      Addr →
      Addr →
      Int →
      Int →
      Int

    no-more-elements :
      (up down : Int) →
      (pointer-memory : Addr → Addr) →
      (item array : Addr) →
      up ≤Z down →
      zeroZ ≤Z up →
      lIndexOf pointer-memory item array down up ≡ up

    found-item :
      (pointer-memory : Addr → Addr) →
      (array : Addr) →
      (down : Int) →
      (item : Addr) →
      (up : Int) →
      pointer-memory (shift array down) ≡ item →
      zeroZ ≤Z down →
      down <Z up →
      lIndexOf pointer-memory item array down up ≡ down

    not-the-item :
      (pointer-memory : Addr → Addr) →
      (array : Addr) →
      (down : Int) →
      (item : Addr) →
      (up : Int) →
      pointer-memory (shift array down) ≠ item →
      zeroZ ≤Z down →
      down <Z up →
      lIndexOf
        pointer-memory item array (addInt oneZ down) up ≡
      lIndexOf pointer-memory item array down up

module VC
  (region : Int → Int)
  (index-of-theory : IndexOfTheory) where

  open IndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (base (pointer-memory p)) ≤Z zeroZ

  goal3 : Set
  goal3 =
    (i1 : Int) →
    (pointer-memory : Addr → Addr) →
    (item array : Addr) →
    (lower-index upper-index prior-index : Int) →
    let next-index = addInt oneZ i1 in
    lIndexOf
      pointer-memory item array lower-index upper-index ≡
      upper-index →
    i1 ≤Z upper-index →
    lower-index ≤Z upper-index →
    i1 <Z upper-index →
    prior-index ≤Z i1 →
    lower-index ≤Z i1 →
    lower-index ≤Z prior-index →
    zeroZ ≤Z lower-index →
    region (base item) ≤Z zeroZ →
    region (base array) ≤Z zeroZ →
    Framed pointer-memory →
    IsSint32 upper-index →
    IsSint32 i1 →
    IsSint32 prior-index →
    IsSint32 lower-index →
    IsSint32 next-index →
    ((index : Int) →
      index <Z i1 →
      lower-index ≤Z index →
      pointer-memory (shift array index) ≠ item) →
    ((index : Int) →
      index <Z i1 →
      lower-index ≤Z index →
      lIndexOf
        pointer-memory item array i1 upper-index ≡
        upper-index) →
    lIndexOf
      pointer-memory item array next-index upper-index ≡
      upper-index

index-of-up-unexisting-item-loop-invariant-3-preserved-goal3 : Set
index-of-up-unexisting-item-loop-invariant-3-preserved-goal3 =
  (region : Int → Int) →
  (index-of-theory : IndexOfTheory) →
  VC.goal3 region index-of-theory
