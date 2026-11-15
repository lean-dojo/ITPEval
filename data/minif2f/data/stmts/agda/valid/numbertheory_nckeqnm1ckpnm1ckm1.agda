-- Statement-only formalization of miniF2F valid problem numbertheory_nckeqnm1ckpnm1ckm1. This
-- file contains no proof.

module numbertheory_nckeqnm1ckpnm1ckm1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 4 _≤_ _<_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

choose : Nat → Nat → Nat
choose zero zero = 1
choose zero (suc k) = 0
choose (suc n) zero = 1
choose (suc n) (suc k) = choose n k + choose n (suc k)

numbertheory_nckeqnm1ckpnm1ckm1 : Set
numbertheory_nckeqnm1ckpnm1ckm1 =
  (n k : Nat) →
  zero < n →
  zero < k →
  k ≤ n →
  choose n k ≡ choose (n - 1) k + choose (n - 1) (k - 1)
