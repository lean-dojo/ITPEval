-- Statement-only formalization of PutnamBench corpus artifact putnam_2009_a5:
-- no finite abelian group has the product of the orders of all its elements
-- equal to 2 raised to the 2009th power. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2009A5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<=N_

data Bottom : Set where

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Finite (A : Set) : Set where
  field
    size :
      Nat
    toFin :
      A ->
      Fin size
    fromFin :
      Fin size ->
      A
    from-to :
      (x : A) ->
      fromFin (toFin x) == x
    to-from :
      (i : Fin size) ->
      toFin (fromFin i) == i

record CommutativeGroup (A : Set) : Set where
  field
    identity :
      A
    multiply :
      A ->
      A ->
      A
    inverse :
      A ->
      A
    associative :
      (x y z : A) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    identity-left :
      (x : A) ->
      multiply identity x == x
    identity-right :
      (x : A) ->
      multiply x identity == x
    inverse-left :
      (x : A) ->
      multiply (inverse x) x == identity
    inverse-right :
      (x : A) ->
      multiply x (inverse x) == identity
    commutative :
      (x y : A) ->
      multiply x y == multiply y x

record FiniteAbelianGroup : Set1 where
  field
    Carrier :
      Set
    group :
      CommutativeGroup Carrier
    finite :
      Finite Carrier

open CommutativeGroup
open Finite
open FiniteAbelianGroup

powerElement :
  (G : FiniteAbelianGroup) ->
  Carrier G ->
  Nat ->
  Carrier G
powerElement G x zero =
  identity (group G)
powerElement G x (suc n) =
  multiply (group G) x (powerElement G x n)

record IsElementOrder
  (G : FiniteAbelianGroup)
  (x : Carrier G)
  (n : Nat) :
  Set where

  field
    order-positive :
      Positive n
    power-is-identity :
      powerElement G x n == identity (group G)
    least-positive-power :
      (k : Nat) ->
      Positive k ->
      powerElement G x k == identity (group G) ->
      n <=N k

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

powerNat : Nat -> Nat -> Nat
powerNat base zero =
  one
powerNat base (suc exponent) =
  base * powerNat base exponent

productFin :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
productFin {zero} term =
  one
productFin {suc n} term =
  term fzero *
  productFin (\ i -> term (fsuc i))

productOfElementOrders :
  (G : FiniteAbelianGroup) ->
  (Carrier G -> Nat) ->
  Nat
productOfElementOrders G order =
  productFin
    (\ i ->
      order (fromFin (finite G) i))

record Counterexample : Set1 where
  field
    finite-abelian-group :
      FiniteAbelianGroup
    element-order :
      Carrier finite-abelian-group ->
      Nat
    element-order-is-exact :
      (x : Carrier finite-abelian-group) ->
      IsElementOrder
        finite-abelian-group
        x
        (element-order x)
    product-equation :
      productOfElementOrders
        finite-abelian-group
        element-order
      ==
      powerNat two 2009

putnam-2009-a5 : Set1
putnam-2009-a5 =
  Counterexample ->
  Bottom
