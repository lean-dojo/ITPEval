-- Statement-only formalization of Logipedia corpus artifact
-- gcd.axiom_gcd_aux_body_S (catalog title "gcd.axiom_gcd_aux_body_S"):
-- at every successor recursion index, the auxiliary greatest-common-divisor
-- body equals the binary natural-number function that returns the second input
-- when it divides the first, and otherwise applies the preceding auxiliary
-- function to that input and their remainder. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_gcd_aux_body_S where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)

eqb : Nat -> Nat -> Bool
eqb zero zero = true
eqb zero (suc n) = false
eqb (suc m) zero = false
eqb (suc m) (suc n) = eqb m n

match-bool-type : {A : Set} -> A -> A -> Bool -> A
match-bool-type case-true case-false true = case-true
match-bool-type case-true case-false false = case-false

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (mod-aux gcd-aux gcd-aux-body : Nat -> Nat -> Nat -> Nat) where

  naturalMod : Nat -> Nat -> Nat
  naturalMod n zero = n
  naturalMod n (suc m) = mod-aux n n m

  dividesb : Nat -> Nat -> Bool
  dividesb n m = eqb (naturalMod m n) zero

  axiom-gcd-aux-body-S : Set
  axiom-gcd-aux-body-S =
    (p : Nat) ->
    equal
      (Nat -> Nat -> Nat)
      (gcd-aux-body (suc p))
      (\ m n ->
        match-bool-type
          n
          (gcd-aux p n (naturalMod m n))
          (dividesb n m))
