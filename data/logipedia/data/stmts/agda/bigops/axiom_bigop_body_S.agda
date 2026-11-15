-- Statement-only formalization of Logipedia corpus artifact bigops.axiom_bigop_body_S
-- (catalog title "bigops.axiom_bigop_body_S"): equality at every successor
-- index between the generic big-operation body and its Boolean-selected
-- recursive step, for every carrier type. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_bigop_body_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc)

Bigop :
  {level : Level} ->
  Set (lsuc level)
Bigop {level} =
  (H : Set level) ->
  Nat ->
  (Nat -> Bool) ->
  H ->
  (H -> H -> H) ->
  (Nat -> H) ->
  H

match-bool-type :
  {level : Level} ->
  {H : Set level} ->
  H ->
  H ->
  Bool ->
  H
match-bool-type case-true case-false true = case-true
match-bool-type case-true case-false false = case-false

module Statement
  {level : Level}
  (equal : (A : Set level) -> A -> A -> Set level)
  (bigop bigop-body : Bigop {level}) where

  axiom-bigop-body-S :
    Set (lsuc level)
  axiom-bigop-body-S =
    (H : Set level) ->
    (n : Nat) ->
    equal
      ((Nat -> Bool) -> H -> (H -> H -> H) -> (Nat -> H) -> H)
      (bigop-body H (suc n))
      (\ p nil op f ->
        match-bool-type
          (op (f n) (bigop H n p nil op f))
          (bigop H n p nil op f)
          (p n))
