-- Statement-only formalization of Logipedia corpus artifact
-- permutation.sym_eq_invert_permut_body_S (catalog title
-- "permutation.sym_eq_invert_permut_body_S"): at each successor index, the
-- function returning that successor when its input equals the successor's
-- image, and otherwise using the preceding inverse-permutation function, is
-- Leibniz-equal to the inverse-permutation body. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_invert_permut_body_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc; zero)

InversePermutation : Set
InversePermutation =
  (Nat -> Nat) -> Nat -> Nat

Leibniz :
  {level : Level} ->
  (A : Set level) ->
  A ->
  A ->
  Set (lsuc level)
Leibniz {level} A x y =
  (P : A -> Set level) ->
  P x ->
  P y

eqb : Nat -> Nat -> Bool
eqb zero zero = true
eqb zero (suc n) = false
eqb (suc m) zero = false
eqb (suc m) (suc n) = eqb m n

match-bool-type : {A : Set} -> A -> A -> Bool -> A
match-bool-type case-true case-false true = case-true
match-bool-type case-true case-false false = case-false

module Statement
  (invert-permut invert-permut-body :
    Nat -> InversePermutation) where

  sym-eq-invert-permut-body-S : Set₁
  sym-eq-invert-permut-body-S =
    (n : Nat) ->
    Leibniz
      InversePermutation
      (\ f m ->
        match-bool-type
          (suc n)
          (invert-permut n f m)
          (eqb m (f (suc n))))
      (invert-permut-body (suc n))
