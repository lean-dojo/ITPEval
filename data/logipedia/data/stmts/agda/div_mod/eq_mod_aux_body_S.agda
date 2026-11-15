-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.eq_mod_aux_body_S (catalog title
-- "div_mod.eq_mod_aux_body_S"): at every successor recursion index, the
-- auxiliary modulus body is Leibniz-equal to the binary natural-number
-- function that returns its first input when it is at most its second, and
-- otherwise returns the recursive auxiliary remainder. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module eq_mod_aux_body_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

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

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

match-bool-type : {A : Set} -> A -> A -> Bool -> A
match-bool-type case-true case-false true = case-true
match-bool-type case-true case-false false = case-false

module Statement
  (mod-aux mod-aux-body : Nat -> Nat -> Nat -> Nat) where

  eq-mod-aux-body-S : Set₁
  eq-mod-aux-body-S =
    (p : Nat) ->
    Leibniz
      (Nat -> Nat -> Nat)
      (mod-aux-body (suc p))
      (\ m n ->
        match-bool-type
          m
          (mod-aux p (m - suc n) n)
          (leb m n))
