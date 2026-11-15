-- Statement-only formalization of miniF2F test problem amc12_2000_p1: three
-- pairwise-distinct natural factors of 2001 have sum at most 671. This file contains no proof.

module amc12-2000-p1 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _<_)

infix 4 _≠_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

amc12-2000-p1 : Set
amc12-2000-p1 =
  (i m o : Nat) →
  i ≠ m →
  m ≠ o →
  o ≠ i →
  i * m * o ≡ 2001 →
  (i + m + o < 672) ≡ true
