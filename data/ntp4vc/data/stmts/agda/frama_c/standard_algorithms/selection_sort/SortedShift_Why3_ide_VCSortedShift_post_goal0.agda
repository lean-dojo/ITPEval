-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/selection_sort/SortedShift_Why3_ide_VCSortedShift_post_goal0:
-- under the stated integer ordering, memory-region, and uint32-range
-- assumptions, a sorted integer-memory interval remains sorted when its
-- address base is shifted to the interval's lower endpoint. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module SortedShift_Why3_ide_VCSortedShift_post_goal0 where

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

zeroZ uint32Upper : Int
zeroZ = pos zero
uint32Upper = pos 4294967296

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

PSorted :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PSorted integer-memory a lower upper =
  (left right : Int) →
  right <Z upper →
  lower ≤Z left →
  left <Z right →
  integer-memory (shift a left) ≤Z integer-memory (shift a right)

Goal0 : (Int → Int) → Set
Goal0 region =
  (i1 : Int) →
  (i : Int) →
  (a : Addr) →
  (integer-memory : Addr → Int) →
  i1 ≤Z i →
  region (base a) ≤Z zeroZ →
  IsUint32 i →
  IsUint32 i1 →
  PSorted integer-memory a i1 i →
  PSorted integer-memory (shift a i1) zeroZ (subtractInt i i1)

sorted-shift-post-goal0 : Set
sorted-shift-post-goal0 =
  (region : Int → Int) →
  Goal0 region
