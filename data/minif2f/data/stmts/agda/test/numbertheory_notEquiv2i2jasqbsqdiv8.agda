-- Statement-only formalization of miniF2F test problem numbertheory_notEquiv2i2jasqbsqdiv8.
-- This file contains no proof.

module numbertheory_notEquiv2i2jasqbsqdiv8 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 2 _↔_
infixr 3 _∧_
infixl 6 _+z_
infixl 7 _*z_

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    left  : A
    right : B

record _↔_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

numbertheory_notEquiv2i2jasqbsqdiv8 : Set
numbertheory_notEquiv2i2jasqbsqdiv8 =
  ¬ ((a b : Int) →
    (Exists Int (λ i →
      Exists Int (λ j →
        (a ≡ pos 2 *z i) ∧
        (b ≡ pos 2 *z j))))
    ↔
    (Exists Int (λ k →
      (a *z a +z b *z b) ≡ pos 8 *z k)))
