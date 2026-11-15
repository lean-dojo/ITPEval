-- Statement-only formalization of Logipedia corpus artifact bigops.bigop_iso
-- (catalog title "bigops.bigop_iso"): invariance of a Boolean-filtered finite
-- product of natural numbers under an isomorphism of its selected indices.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module bigop_iso where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Primitive using (Level)

infix 4 _<_
infixr 3 _∧_

data _<_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero < suc n
  succ<succ : {m n : Nat} -> m < n -> suc m < suc n

record _∧_ (A B : Set) : Set where
  field
    first  : A
    second : B

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

sub-hk :
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Nat ->
  Nat ->
  (Nat -> Bool) ->
  (Nat -> Bool) ->
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Set
sub-hk h k n1 n2 p1 p2 f1 f2 =
  (i : Nat) ->
  i < n1 ->
  p1 i ≡ true ->
  ((h i < n2) ∧ (p2 (h i) ≡ true)) ∧
  (k (h i) ≡ i)

iso :
  Nat ->
  Nat ->
  (Nat -> Bool) ->
  (Nat -> Bool) ->
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Set
iso n1 n2 p1 p2 f1 f2 =
  Σ (Nat -> Nat) (\ h ->
    Σ (Nat -> Nat) (\ k ->
      (((i : Nat) ->
          i < n1 ->
          p1 i ≡ true ->
          f1 i ≡ f2 (h i))
       ∧ sub-hk h k n1 n2 p1 p2 f1 f2)
      ∧ sub-hk k h n2 n1 p2 p1 f2 f1))

bigop-iso : Set
bigop-iso =
  (n1 n2 : Nat) ->
  (p1 p2 : Nat -> Bool) ->
  (f1 f2 : Nat -> Nat) ->
  iso n1 n2 p1 p2 f1 f2 ->
  bigop n1 p1 1 _*_ f1 ≡
  bigop n2 p2 1 _*_ f2
