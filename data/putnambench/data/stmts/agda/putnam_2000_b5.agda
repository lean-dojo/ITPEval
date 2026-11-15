-- Statement-only formalization of PutnamBench corpus artifact putnam_2000_b5
-- (putnambench__agda__putnam_2000_b5): finite positive-integer sets evolving
-- by exclusive membership under a unit shift recur as the union of the
-- initial set with its translation. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2000B5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  (member : Int -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      Int
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (x : Int) ->
      member x ->
      Exists (Fin cardinality)
        (\ index -> x == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

Finite :
  (Int -> Set) ->
  Set
Finite member =
  Exists Nat
    (\ cardinality ->
      HasCardinality member cardinality)

data PositiveInteger : Int -> Set where
  positive :
    {n : Nat} ->
    PositiveInteger (pos (suc n))

predecessor : Int -> Int
predecessor (pos zero) =
  negsuc zero
predecessor (pos (suc n)) =
  pos n
predecessor (negsuc n) =
  negsuc (suc n)

subtractNat : Int -> Nat -> Int
subtractNat x zero =
  x
subtractNat x (suc n) =
  subtractNat (predecessor x) n

Exclusive : Set -> Set -> Set
Exclusive A B =
  (A and Not B) or (B and Not A)

ExtensionalEqual :
  (Int -> Set) ->
  (Int -> Set) ->
  Set
ExtensionalEqual left-set right-set =
  (x : Int) ->
  Iff (left-set x) (right-set x)

putnam-2000-b5 : Set1
putnam-2000-b5 =
  (S : Nat -> Int -> Set) ->
  ((n : Nat) -> Finite (S n)) ->
  ((n : Nat) ->
    (s : Int) ->
    S n s ->
    PositiveInteger s) ->
  ((n : Nat) ->
    (a : Int) ->
    Iff
      (S (suc n) a)
      (Exclusive
        (S n (predecessor a))
        (S n a))) ->
  (n : Nat) ->
  Exists Nat
    (\ N ->
      (n <=N N)
      and
      ExtensionalEqual
        (S N)
        (\ M ->
          (S zero M)
          or
          (S zero (subtractNat M N))))
