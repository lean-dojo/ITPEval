-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.axiom_div_aux_body_S (catalog title
-- "div_mod.axiom_div_aux_body_S"): at every successor recursion index, the
-- auxiliary division body equals the binary natural-number function that
-- returns zero when its first input is at most its second, and otherwise
-- returns the successor of the recursive auxiliary quotient. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module axiom_div_aux_body_S where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

match-bool-type : {A : Set} -> A -> A -> Bool -> A
match-bool-type case-true case-false true = case-true
match-bool-type case-true case-false false = case-false

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (div-aux div-aux-body : Nat -> Nat -> Nat -> Nat) where

  axiom-div-aux-body-S : Set
  axiom-div-aux-body-S =
    (p : Nat) ->
    equal
      (Nat -> Nat -> Nat)
      (div-aux-body (suc p))
      (\ m n ->
        match-bool-type
          zero
          (suc (div-aux p (m - suc n) n))
          (leb m n))
