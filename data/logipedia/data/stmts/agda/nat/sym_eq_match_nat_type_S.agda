-- Statement-only formalization of Logipedia corpus artifact
-- nat.sym_eq_match_nat_type_S (catalog title
-- "nat.sym_eq_match_nat_type_S"): for every result type, pair of
-- natural-number branches, and natural number n, the successor branch at n
-- is Leibniz-equal to matching the successor of n. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module sym_eq_match_nat_type_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; suc)

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
  {return-level : Level}
  (match-nat-type :
    (A : Set return-level) ->
    A ->
    (Nat -> A) ->
    Nat ->
    A) where

  sym-eq-match-nat-type-S :
    Set (lsuc return-level)
  sym-eq-match-nat-type-S =
    (return-type : Set return-level) ->
    (case-O : return-type) ->
    (case-S : Nat -> return-type) ->
    (n : Nat) ->
    Leibniz
      return-type
      (case-S n)
      (match-nat-type return-type case-O case-S (suc n))
