-- Statement-only formalization of miniF2F valid problem imo_1993_p5: existence of a
-- strictly order-preserving function on natural numbers satisfying its specified initial
-- value and iteration equation. This file contains no proof.

module imo-1993-p5 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤_ _<_
infix 2 _↔_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

record _↔_ (A B : Set) : Set where
  field
    forward : A → B
    backward : B → A

record IMO1993P5 : Set where
  field
    f : Nat → Nat
    order-embedding :
      (a b : Nat) → (a < b) ↔ (f a < f b)
    value-at-one :
      f 1 ≡ 2
    iteration-equation :
      (n : Nat) → f (f n) ≡ f n + n

imo-1993-p5 : Set
imo-1993-p5 = IMO1993P5
