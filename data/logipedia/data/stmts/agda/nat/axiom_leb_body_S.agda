-- Statement-only formalization of Logipedia corpus artifact
-- nat.axiom_leb_body_S (catalog title "nat.axiom_leb_body_S"): for every
-- natural number, the Boolean less-than-or-equal body at its successor is
-- related by the source equality proposition to the function returning false
-- at zero and less-than-or-equal with its predecessor at each successor. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module axiom_leb_body_S where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool; false)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (match-nat-type : (A : Set) -> A -> (Nat -> A) -> Nat -> A)
  (leb leb-body : Nat -> Nat -> Bool) where

  axiom-leb-body-S : Set
  axiom-leb-body-S =
    (n : Nat) ->
    equal
      (Nat -> Bool)
      (leb-body (suc n))
      (\ m -> match-nat-type Bool false (\ q -> leb n q) m)
