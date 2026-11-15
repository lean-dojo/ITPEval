-- Statement-only formalization of "The Binomial Theorem" from Hundred Theorems item 044. This
-- file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

one : Nat
one = suc zero

power : Nat → Nat → Nat
power x zero = one
power x (suc n) = power x n * x

choose : Nat → Nat → Nat
choose n zero = one
choose zero (suc k) = zero
choose (suc n) (suc k) = choose n (suc k) + choose n k

sum-through : Nat → (Nat → Nat) → Nat
sum-through zero term = term zero
sum-through (suc n) term =
  sum-through n term + term (suc n)

binomial-term : Nat → Nat → Nat → Nat → Nat
binomial-term n x y k =
  choose n k * power x k * power y (n - k)

binomial-expansion : Nat → Nat → Nat → Nat
binomial-expansion n x y =
  sum-through n (binomial-term n x y)

the-binomial-theorem : Set
the-binomial-theorem =
  (n x y : Nat) →
  power (x + y) n ≡ binomial-expansion n x y
