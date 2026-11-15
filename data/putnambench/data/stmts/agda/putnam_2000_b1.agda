-- Statement-only formalization of PutnamBench corpus artifact putnam_2000_b1:
-- among integer triples with at least one odd coordinate, some integer linear
-- combination is odd on at least four sevenths of the finite index set. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2000B1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_
infixr 3 _and_
infixr 2 _or_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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
  {A : Set}
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

data Odd : Int -> Set where
  positive-odd :
    (k : Nat) ->
    Odd (pos (suc (k + k)))
  negative-odd :
    (k : Nat) ->
    Odd (negsuc (k + k))

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

four : Nat
four =
  two + two

seven : Nat
seven =
  suc (suc (suc (suc (suc (suc one)))))

linearCombination :
  {N : Nat} ->
  (Fin N -> Int) ->
  (Fin N -> Int) ->
  (Fin N -> Int) ->
  Int ->
  Int ->
  Int ->
  Fin N ->
  Int
linearCombination a b c r s t j =
  addInt
    (addInt
      (multiplyInt r (a j))
      (multiplyInt s (b j)))
    (multiplyInt t (c j))

putnam-2000-b1 : Set
putnam-2000-b1 =
  (N : Nat) ->
  (a b c : Fin N -> Int) ->
  one <=N N ->
  ((j : Fin N) ->
    Odd (a j) or Odd (b j) or Odd (c j)) ->
  Exists Int
    (\ r ->
      Exists Int
        (\ s ->
          Exists Int
            (\ t ->
              Exists Nat
                (\ count ->
                  HasCardinality
                    (\ j ->
                      Odd
                        (linearCombination
                          a b c r s t j))
                    count
                  and
                  (four * N) <=N (seven * count)))))
