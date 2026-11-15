-- Statement-only formalization of Hundred Theorems artifact
-- hundred-theorems__agda__074, "The Principle of Mathematical Induction":
-- a predicate on the natural numbers follows everywhere from its zero case
-- and successor step. This file contains no proof.

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)

the-principle-of-mathematical-induction : {ℓ : Level} → Set (lsuc ℓ)
the-principle-of-mathematical-induction {ℓ} =
  {P : Nat → Set ℓ} →
  P zero →
  ((n : Nat) → P n → P (suc n)) →
  (n : Nat) → P n
