-- Statement-only formalization of miniF2F test problem aime_1984_p7. This file contains no
-- proof.

module aime-1984-p7 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_; _<_)

aime-1984-p7 : Set
aime-1984-p7 =
  (f : Nat → Nat) →
  ((n : Nat) → (1000 < suc n) ≡ true → f n ≡ n - 3) →
  ((n : Nat) → (n < 1000) ≡ true → f n ≡ f (f (n + 5))) →
  f 84 ≡ 997
