-- Statement-only formalization of miniF2F test problem mathd_numbertheory_495:
-- positive naturals ending in 2 and 4 with gcd 6 have lcm at least 108. This
-- file contains no proof.

module mathd-numbertheory-495 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

infix 4 _≤_ _<_ _∣_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

record IsGCD (a b g : Nat) : Set where
  field
    gcd-divides-left : g ∣ a
    gcd-divides-right : g ∣ b
    greatest-common-divisor :
      (d : Nat) →
      d ∣ a →
      d ∣ b →
      d ∣ g

record IsLCM (a b l : Nat) : Set where
  field
    lcm-left-divides : a ∣ l
    lcm-right-divides : b ∣ l
    least-common-multiple :
      (k : Nat) →
      a ∣ k →
      b ∣ k →
      l ∣ k

mathd-numbertheory-495 : Set
mathd-numbertheory-495 =
  (a b : Nat) →
  zero < a →
  zero < b →
  naturalMod a 10 ≡ 2 →
  naturalMod b 10 ≡ 4 →
  IsGCD a b 6 →
  (l : Nat) →
  IsLCM a b l →
  108 ≤ l
