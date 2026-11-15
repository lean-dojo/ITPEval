-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_pop_Why3_ide_VClist_pop_more_post_3_part1_goal16:
-- updating the popped list head in pointer memory preserves the inductive
-- linked-list segment with its length decreased by one, under the stated
-- memory-validity, separation, framing, linked-allocation, and bounds assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module ListPopWhy3IdeVCListPopMorePost3Part1Goal16 where

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

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

andBool : Bool → Bool → Bool
andBool true b = b
andBool false _ = false

ifBool : {A : Set} → Bool → A → A → A
ifBool true yes _ = yes
ifBool false _ no = no

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

addrEqual : Addr → Addr → Bool
addrEqual p q =
  andBool
    (intEqual (base p) (base q))
    (intEqual (offset p) (offset q))

update : {A : Set} → (Addr → A) → Addr → A → Addr → A
update memory location value query =
  ifBool (addrEqual query location) value (memory query)

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

  goal16 : Set
  goal16 =
    (pointer-memory : Addr → Addr) →
    (post-memory : Addr → Addr) →
    (item array : Addr) →
    (length start-index : Int) →
    (allocation : Int → Int) →
    let
      root = pointer-memory item
      array-start = shift array zeroZ
      upper-index = addInt length start-index
      new-root = pointer-memory (shift root zeroZ)
      updated-memory = update post-memory item new-root
    in
    root ≠ addr zeroZ zeroZ →
    zeroZ <Z length →
    zeroZ ≤Z start-index →
    region (base item) ≤Z zeroZ →
    region (base array) ≤Z zeroZ →
    Framed pointer-memory →
    linked allocation →
    IsSint32 length →
    IsSint32 start-index →
    ValidRW allocation item oneZ →
    ValidRW allocation array-start maximumArrayIndex →
    Separated item oneZ array-start maximumArrayIndex →
    Separated root fourZ array-start maximumArrayIndex →
    PLinkedN
      allocation
      pointer-memory
      root
      array
      start-index
      length
      (addr zeroZ zeroZ) →
    ((index : Int) →
      start-index ≤Z index →
      index <Z upper-index →
      Separated
        item oneZ
        (pointer-memory (shift array index)) fourZ) →
    ((index : Int) →
      start-index ≤Z index →
      index <Z upper-index →
      Separated
        (pointer-memory (shift array index)) fourZ
        array-start maximumArrayIndex) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      start-index ≤Z right-index →
      start-index ≤Z left-index →
      right-index <Z upper-index →
      left-index <Z upper-index →
      pointer-memory (shift array left-index) ≠
      pointer-memory (shift array right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      start-index ≤Z right-index →
      start-index ≤Z left-index →
      right-index <Z upper-index →
      left-index <Z upper-index →
      Separated
        (pointer-memory (shift array left-index)) fourZ
        (pointer-memory (shift array right-index)) fourZ) →
    PLinkedN
      allocation
      post-memory
      new-root
      array
      start-index
      (subtractInt length oneZ)
      (addr zeroZ zeroZ) →
    ((index : Int) →
      start-index ≤Z index →
      index <Z addInt start-index (subtractInt length oneZ) →
      Separated
        item oneZ
        (post-memory (shift array index)) fourZ) →
    PLinkedN
      allocation
      updated-memory
      new-root
      array
      start-index
      (subtractInt length oneZ)
      (addr zeroZ zeroZ)

list-pop-more-post-3-part1-goal16 : Set₁
list-pop-more-post-3-part1-goal16 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  VC.goal16 region linked
