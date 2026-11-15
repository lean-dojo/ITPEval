-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/int_sqrt_Why3_ide_VCint_sqrt_loop_term_decrease_goal1:
-- decrease of the integer-square-root loop variant: under the stated
-- unsigned-64 bounds, a nonzero integer is strictly decreased by a logical
-- right shift of two bits. This file contains no proof.

{-# OPTIONS --safe #-}

module int_sqrt_Why3_ide_VCint_sqrt_loop_term_decrease_goal1 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

zeroZ twoZ uint64Upper : Int
zeroZ = pos zero
twoZ = pos (suc (suc zero))
uint64Upper = pos 18446744073709551616

IsUint64 : Int → Set
IsUint64 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint64Upper)

divideByFour : Nat → Nat
divideByFour zero = zero
divideByFour (suc zero) = zero
divideByFour (suc (suc zero)) = zero
divideByFour (suc (suc (suc zero))) = zero
divideByFour (suc (suc (suc (suc n)))) = suc (divideByFour n)

logicalShiftRightByTwo : Int → Int
logicalShiftRightByTwo (pos n) = pos (divideByFour n)
logicalShiftRightByTwo (negsuc _) = zeroZ

Goal1 : Set
Goal1 =
  (i₁ i : Int) →
  let x = logicalShiftRightByTwo i₁
  in
  i₁ ≠ zeroZ →
  twoZ ≤Z i →
  IsUint64 i →
  IsUint64 i₁ →
  IsUint64 x →
  x <Z i₁

int-sqrt-loop-term-decrease-goal1 : Set
int-sqrt-loop-term-decrease-goal1 = Goal1
