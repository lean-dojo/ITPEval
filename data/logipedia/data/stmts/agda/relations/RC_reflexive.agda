-- Statement-only formalization of Logipedia corpus artifact
-- relations.RC_reflexive (catalog title "relations.RC_reflexive"): adjoining
-- equality to an arbitrary binary relation yields a reflexive relation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module RC_reflexive where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

infixr 2 _∨_

data _∨_ {p q : Level} (P : Set p) (Q : Set q) : Set (p ⊔ q) where
  left : P -> P ∨ Q
  right : Q -> P ∨ Q

Reflexive :
  {a r : Level} {A : Set a} ->
  (A -> A -> Set r) ->
  Set (a ⊔ r)
Reflexive {A = A} relation =
  (x : A) -> relation x x

RC :
  {a r : Level} {A : Set a} ->
  (A -> A -> Set r) ->
  A ->
  A ->
  Set (a ⊔ r)
RC relation x y =
  relation x y ∨ x ≡ y

relations-RC-reflexive :
  {a r : Level} ->
  Set (lsuc a ⊔ lsuc r)
relations-RC-reflexive {a} {r} =
  (A : Set a) ->
  (R : A -> A -> Set r) ->
  Reflexive (RC R)
