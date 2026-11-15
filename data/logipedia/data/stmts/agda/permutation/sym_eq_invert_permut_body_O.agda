-- Statement-only formalization of Logipedia corpus artifact
-- permutation.sym_eq_invert_permut_body_O (catalog title
-- "permutation.sym_eq_invert_permut_body_O"): the function that returns zero
-- after comparing its natural input with the image of zero is Leibniz-equal
-- to the inverse-permutation body at zero. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_invert_permut_body_O where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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
  (invert-permut-body :
    Nat -> (Nat -> Nat) -> Nat -> Nat) where

  sym-eq-invert-permut-body-O : Set₁
  sym-eq-invert-permut-body-O =
    Leibniz
      ((Nat -> Nat) -> Nat -> Nat)
      (\ f m ->
        match-bool-type zero zero (eqb m (f zero)))
      (invert-permut-body zero)
