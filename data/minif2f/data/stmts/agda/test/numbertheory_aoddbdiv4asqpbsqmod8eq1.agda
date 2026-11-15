-- Statement-only formalization of miniF2F test problem numbertheory_aoddbdiv4asqpbsqmod8eq1:
-- if a is an odd integer and b is a nonnegative multiple of 4, then a squared plus
-- b squared has remainder 1 modulo 8. This file contains no proof.

module numbertheory_aoddbdiv4asqpbsqmod8eq1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _∣_

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

magnitude : Int → Nat
magnitude (pos n) = n
magnitude (negsuc n) = suc n

Odd : Int → Set
Odd a = Exists Nat (λ k → magnitude a ≡ 2 * k + 1)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

mod8 : Nat → Nat
mod8 n = mod-helper zero 7 n 7

numbertheory_aoddbdiv4asqpbsqmod8eq1 : Set
numbertheory_aoddbdiv4asqpbsqmod8eq1 =
  (a : Int) →
  (b : Nat) →
  Odd a →
  4 ∣ b →
  mod8 (magnitude a * magnitude a + b * b) ≡ 1
