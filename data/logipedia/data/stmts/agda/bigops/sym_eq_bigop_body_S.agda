-- Statement-only formalization of Logipedia corpus artifact bigops.sym_eq_bigop_body_S
-- (catalog title "bigops.sym_eq_bigop_body_S"): Leibniz equality at every
-- successor index from the Boolean-selected recursive step to the generic
-- big-operation body, for every carrier type. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_bigop_body_S where

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
  (bigop bigop-body : Bigop {level}) where

  sym-eq-bigop-body-S :
    Set (lsuc level)
  sym-eq-bigop-body-S =
    (H : Set level) ->
    (n : Nat) ->
    Leibniz
      ((Nat -> Bool) -> H -> (H -> H -> H) -> (Nat -> H) -> H)
      (\ p nil op f ->
        match-bool-type
          (op (f n) (bigop H n p nil op f))
          (bigop H n p nil op f)
          (p n))
      (bigop-body H (suc n))
