-- Statement-only formalization of Logipedia corpus artifact bigops.sym_eq_bigop_S
-- (catalog title "bigops.sym_eq_bigop_S"): Leibniz equality at every successor
-- index from the generic big-operation body to the big-operation function,
-- for every carrier type. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_bigop_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool)
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

module Statement
  {level : Level}
  (bigop bigop-body : Bigop {level}) where

  sym-eq-bigop-S :
    Set (lsuc level)
  sym-eq-bigop-S =
    (H : Set level) ->
    (n : Nat) ->
    Leibniz
      ((Nat -> Bool) -> H -> (H -> H -> H) -> (Nat -> H) -> H)
      (bigop-body H (suc n))
      (bigop H (suc n))
