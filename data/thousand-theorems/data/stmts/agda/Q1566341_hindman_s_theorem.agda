-- Statement-only formalization of thousand-theorems corpus artifact Q1566341
-- (thousand-theorems__agda__Q1566341), "Hindman's theorem": the finite-products
-- set of a stream in any semigroup is partition regular under every finite
-- cover. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1566341_hindman_s_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _×_
infix 2 _↔_

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record _↔_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor iff
  field
    forward  : A -> B
    backward : B -> A

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Semigroup
  {m : Level}
  (M : Set m) :
  Set m where

  field
    multiply : M -> M -> M
    associative :
      (x y z : M) ->
      multiply (multiply x y) z ≡
      multiply x (multiply y z)

open Semigroup

Stream :
  {m : Level} ->
  Set m ->
  Set m
Stream M =
  Nat -> M

head :
  {m : Level} ->
  {M : Set m} ->
  Stream M ->
  M
head stream =
  stream zero

tail :
  {m : Level} ->
  {M : Set m} ->
  Stream M ->
  Stream M
tail stream n =
  stream (suc n)

data FiniteProducts
  {m : Level}
  {M : Set m}
  (semigroup : Semigroup M) :
  Stream M ->
  M ->
  Set m where

  head-product :
    (stream : Stream M) ->
    FiniteProducts semigroup stream (head stream)

  tail-product :
    {stream : Stream M} ->
    {product : M} ->
    FiniteProducts semigroup (tail stream) product ->
    FiniteProducts semigroup stream product

  cons-product :
    {stream : Stream M} ->
    {product : M} ->
    FiniteProducts semigroup (tail stream) product ->
    FiniteProducts semigroup stream
      (multiply semigroup (head stream) product)

Subset :
  {m : Level} ->
  Set m ->
  Set (lsuc m)
Subset {m} M =
  M -> Set m

Family :
  {m : Level} ->
  Set m ->
  Set (lsuc (lsuc m))
Family {m} M =
  Subset M -> Set (lsuc m)

SubsetEquivalent :
  {m : Level} ->
  {M : Set m} ->
  Subset M ->
  Subset M ->
  Set m
SubsetEquivalent {M = M} left right =
  (x : M) ->
  left x ↔ right x

record FiniteFamily
  {m : Level}
  {M : Set m}
  (family : Family M) :
  Set (lsuc (lsuc m)) where

  field
    size : Nat
    enumerate : Fin size -> Subset M
    exactly-enumerated :
      (candidate : Subset M) ->
      family candidate ↔
      Σ (Fin size)
        (λ index ->
          SubsetEquivalent candidate (enumerate index))

Contained :
  {a p q : Level} ->
  {A : Set a} ->
  (A -> Set p) ->
  (A -> Set q) ->
  Set (a ⊔ p ⊔ q)
Contained {A = A} left right =
  (x : A) ->
  left x ->
  right x

CoveredBy :
  {m : Level} ->
  {M : Set m} ->
  Family M ->
  Subset M ->
  Set (lsuc m)
CoveredBy {M = M} family covered =
  (x : M) ->
  covered x ->
  Σ (Subset M)
    (λ member ->
      family member × member x)

hindmans-theorem :
  (m : Level) ->
  Set (lsuc (lsuc m))
hindmans-theorem m =
  (M : Set m) ->
  (semigroup : Semigroup M) ->
  (stream : Stream M) ->
  (cover : Family M) ->
  FiniteFamily cover ->
  CoveredBy cover (FiniteProducts semigroup stream) ->
  Σ (Subset M)
    (λ cell ->
      cover cell ×
      Σ (Stream M)
        (λ monochromatic-stream ->
          Contained
            (FiniteProducts semigroup monochromatic-stream)
            cell))
