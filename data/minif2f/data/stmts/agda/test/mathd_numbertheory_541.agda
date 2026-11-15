-- Statement-only formalization of miniF2F test problem mathd_numbertheory_541. This file
-- contains no proof.

module mathd-numbertheory-541 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _<_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

mathd-numbertheory-541 : Set
mathd-numbertheory-541 =
  (m n : Nat) →
  1 < m →
  1 < n →
  m * n ≡ 2005 →
  m + n ≡ 406
