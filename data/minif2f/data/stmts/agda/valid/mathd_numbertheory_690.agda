-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_690:
-- 314 is the least positive natural number with remainders 2, 4, 6, and 8
-- modulo 3, 5, 7, and 9, respectively. This file contains no proof.

module mathd-numbertheory-690 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

infix 4 _≤_ _<_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

record Solution (n : Nat) : Set where
  field
    positive : zero < n
    modulo-three : naturalMod n 3 ≡ 2
    modulo-five : naturalMod n 5 ≡ 4
    modulo-seven : naturalMod n 7 ≡ 6
    modulo-nine : naturalMod n 9 ≡ 8

record IsLeast (P : Nat → Set) (n : Nat) : Set where
  field
    member : P n
    lower-bound : (m : Nat) → P m → n ≤ m

mathd-numbertheory-690 : Set
mathd-numbertheory-690 = IsLeast Solution 314
