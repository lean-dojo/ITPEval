-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_64: 39 is
-- the least natural number x such that 30 * x is congruent to 42 modulo 47. This file
-- contains no proof.

module mathd-numbertheory-64 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

infix 4 _≤_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

record IsLeast (P : Nat → Set) (n : Nat) : Set where
  field
    member : P n
    lower-bound : (m : Nat) → P m → n ≤ m

Solution : Nat → Set
Solution x = naturalMod (30 * x) 47 ≡ 42

mathd-numbertheory-64 : Set
mathd-numbertheory-64 = IsLeast Solution 39
