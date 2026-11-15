-- Statement-only formalization of Logipedia corpus artifact permutation.injn_Sn_n
-- (catalog title "permutation.injn_Sn_n"): bounded injectivity of a
-- natural-number endofunction through suc n implies bounded injectivity
-- through n. This file contains no proof.

{-# OPTIONS --safe #-}

module injn_Sn_n where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤_

data _≤_ : Nat -> Nat -> Set where
  zero≤   : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

Injn : (Nat -> Nat) -> Nat -> Set
Injn f bound =
  (i j : Nat) ->
  i ≤ bound ->
  j ≤ bound ->
  f i ≡ f j ->
  i ≡ j

injn-Sn-n : Set
injn-Sn-n =
  (f : Nat -> Nat) ->
  (n : Nat) ->
  Injn f (suc n) ->
  Injn f n
