-- Statement-only formalization of miniF2F test problem
-- numbertheory_3pow2pownm1mod2pownp3eq2pownp2: for positive n, the remainder
-- of 3^(2^n) - 1 modulo 2^(n + 3) equals 2^(n + 2). This file contains no proof.

module numbertheory_3pow2pownm1mod2pownp3eq2pownp2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; mod-helper)

infix 4 _≤_ _<_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

numbertheory_3pow2pownm1mod2pownp3eq2pownp2 : Set
numbertheory_3pow2pownm1mod2pownp3eq2pownp2 =
  (n : Nat) →
  zero < n →
  naturalMod (3 ^ (2 ^ n) - 1) (2 ^ (n + 3)) ≡ 2 ^ (n + 2)
