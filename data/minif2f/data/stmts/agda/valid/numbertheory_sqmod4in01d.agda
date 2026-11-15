-- Statement-only formalization of miniF2F valid problem numbertheory_sqmod4in01d. This file
-- contains no proof.

module numbertheory_sqmod4in01d where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

infixr 2 _∨_

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

magnitude : Int → Nat
magnitude (pos n) = n
magnitude (negsuc n) = suc n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

squareMod4 : Int → Nat
squareMod4 a =
  naturalMod (magnitude a * magnitude a) 4

numbertheory_sqmod4in01d : Set
numbertheory_sqmod4in01d =
  (a : Int) →
  squareMod4 a ≡ 0 ∨ squareMod4 a ≡ 1
