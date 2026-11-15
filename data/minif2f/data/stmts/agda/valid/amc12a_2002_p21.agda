-- Statement-only formalization of miniF2F valid problem amc12a_2002_p21. This file contains no
-- proof.

module amc12a-2002-p21 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _<_; mod-helper)

infix 4 _≤_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

NatLess : Nat → Nat → Set
NatLess m n = (m < n) ≡ true

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

sumFirst : Nat → (Nat → Nat) → Nat
sumFirst zero term = zero
sumFirst (suc n) term = sumFirst n term + term n

amc12a-2002-p21 : Set
amc12a-2002-p21 =
  (u : Nat → Nat) →
  u 0 ≡ 4 →
  u 1 ≡ 7 →
  ((n : Nat) →
    u (n + 2) ≡ naturalMod (u n + u (n + 1)) 10) →
  (n : Nat) →
  NatLess 10000 (sumFirst n u) →
  1999 ≤ n
