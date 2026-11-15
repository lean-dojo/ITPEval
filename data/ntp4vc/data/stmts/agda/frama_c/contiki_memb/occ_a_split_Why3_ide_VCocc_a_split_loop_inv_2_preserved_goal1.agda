-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_memb/occ_a_split_Why3_ide_VCocc_a_split_loop_inv_2_preserved_goal1:
-- under the stated interval-splitting equality, index bounds, memory-region
-- condition, constancy, and signed 32-bit range assumptions, advancing the
-- upper endpoint preserves the occurrence-count split. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module occ-a-split-Why3-ide-VCocc-a-split-loop-inv-2-preserved-goal1 where

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

signed32Lower signed32Upper signed32MaximumMinusOne : Int
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
signed32MaximumMinusOne = pos 2147483646

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

record OccArrayTheory : Set where
  field
    lOccA : (Addr → Int) → Int → Addr → Int → Int → Int

    end-occ :
      (upper lower : Int) →
      (memory : Addr → Int) →
      (element : Int) →
      (start : Addr) →
      upper ≤Z lower →
      lOccA memory element start lower upper ≡ zeroZ

    iter-occ-true :
      (upper : Int) →
      (memory : Addr → Int) →
      (start : Addr) →
      (element lower : Int) →
      memory (shift start (subtractInt upper oneZ)) ≡ element →
      lower <Z upper →
      addInt oneZ
        (lOccA memory element start lower (subtractInt upper oneZ))
        ≡
      lOccA memory element start lower upper

    iter-occ-false :
      (upper : Int) →
      (memory : Addr → Int) →
      (start : Addr) →
      (element lower : Int) →
      memory (shift start (subtractInt upper oneZ)) ≠ element →
      lower <Z upper →
      lOccA memory element start lower (subtractInt upper oneZ)
        ≡
      lOccA memory element start lower upper

open OccArrayTheory

Goal1 :
  OccArrayTheory →
  (Int → Int) →
  ((Addr → Int) → Set) →
  Set
Goal1 occurrence-theory region sconst =
  (t : Addr → Int) →
  (i₃ : Int) →
  (a : Addr) →
  (i₂ i₄ i₁ i : Int) →
  let
    x = lOccA occurrence-theory t i₃ a i₂ i₄
    x₁ = addInt oneZ i₁
  in
  addInt x (lOccA occurrence-theory t i₃ a i₄ i₁)
    ≡
  lOccA occurrence-theory t i₃ a i₂ i₁ →
  i₁ ≤Z i →
  i₄ ≤Z i →
  i₁ <Z i →
  i₄ ≤Z i₁ →
  i₂ ≤Z i₄ →
  region (base a) ≤Z zeroZ →
  i₁ ≤Z signed32MaximumMinusOne →
  sconst t →
  IsSint32 i →
  IsSint32 i₁ →
  IsSint32 i₂ →
  IsSint32 i₃ →
  IsSint32 i₄ →
  IsSint32 x₁ →
  addInt x (lOccA occurrence-theory t i₃ a i₄ x₁)
    ≡
  lOccA occurrence-theory t i₃ a i₂ x₁

occ-a-split-loop-inv-2-preserved-goal1 : Set₁
occ-a-split-loop-inv-2-preserved-goal1 =
  (occurrence-theory : OccArrayTheory) →
  (region : Int → Int) →
  (sconst : (Addr → Int) → Set) →
  Goal1 occurrence-theory region sconst
