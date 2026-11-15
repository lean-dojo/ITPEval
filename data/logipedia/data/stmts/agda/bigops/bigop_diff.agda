-- Statement-only formalization of Logipedia corpus artifact bigops.bigop_diff
-- (catalog title "bigops.bigop_diff"): removing a selected factor from a
-- Boolean-filtered finite product of natural numbers. This file contains no proof.

{-# OPTIONS --safe #-}

module bigop_diff where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<_
infixr 6 _and_

data _<_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero < suc n
  succ<succ : {m n : Nat} -> m < n -> suc m < suc n

not : Bool -> Bool
not true = false
not false = true

_and_ : Bool -> Bool -> Bool
true and q = q
false and q = false

eqb : Nat -> Nat -> Bool
eqb zero zero = true
eqb zero (suc n) = false
eqb (suc m) zero = false
eqb (suc m) (suc n) = eqb m n

bigop :
  {level : Level} ->
  {H : Set level} ->
  Nat ->
  (Nat -> Bool) ->
  H ->
  (H -> H -> H) ->
  (Nat -> H) ->
  H
bigop zero p nil op f = nil
bigop (suc n) p nil op f with p n
... | true = op (f n) (bigop n p nil op f)
... | false = bigop n p nil op f

bigop-diff : Set
bigop-diff =
  (p : Nat -> Bool) ->
  (f : Nat -> Nat) ->
  (i n : Nat) ->
  i < n ->
  p i == true ->
  bigop n p 1 _*_ f ==
  f i * bigop n (\ x -> not (eqb i x) and p x) 1 _*_ f
