-- Statement-only formalization of thousand-theorems corpus artifact Q1077462,
-- "König's theorem (set theory)": pointwise strict cardinal inequalities between
-- arbitrary type families imply that their dependent sum has strictly smaller
-- cardinality than their dependent product. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1077462_k_nig_s_theorem_set_theory where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not proposition =
  proposition -> Bottom

Injective :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (A -> B) ->
  Set (a ⊔ b)
Injective {A = A} function =
  (x y : A) ->
  function x ≡ function y ->
  x ≡ y

record Injection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    map       : A -> B
    injective : Injective map

record StrictlySmaller
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    embeds       : Injection A B
    no-embedding : Not (Injection B A)

koenigs-theorem :
  {i c : Level} ->
  Set (lsuc (i ⊔ c))
koenigs-theorem {i} {c} =
  (I : Set i) ->
  (A : I -> Set c) ->
  (B : I -> Set c) ->
  ((index : I) -> StrictlySmaller (A index) (B index)) ->
  StrictlySmaller
    (Σ I A)
    ((index : I) -> B index)
