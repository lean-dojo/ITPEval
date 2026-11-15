-- Statement-only formalization of PutnamBench corpus artifact putnam_1979_a1:
-- among nonempty finite multisets of positive natural numbers summing to 1979,
-- the greatest product is attained by one 2 and 659 copies of 3. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

data Nonempty {A : Set} : List A -> Set where
  nonempty :
    {x : A} ->
    {xs : List A} ->
    Nonempty (x ∷ xs)

data All {A : Set} (P : A -> Set) : List A -> Set where
  all[] :
    All P []
  all∷ :
    {x : A} ->
    {xs : List A} ->
    P x ->
    All P xs ->
    All P (x ∷ xs)

Positive : Nat -> Set
Positive n =
  suc zero <= n

sumList : List Nat -> Nat
sumList [] =
  zero
sumList (x ∷ xs) =
  x + sumList xs

productList : List Nat -> Nat
productList [] =
  suc zero
productList (x ∷ xs) =
  x * productList xs

replicate : Nat -> Nat -> List Nat
replicate zero value =
  []
replicate (suc count) value =
  value ∷ replicate count value

putnam-1979-a1-solution : List Nat
putnam-1979-a1-solution =
  2 ∷ replicate 659 3

Admissible : List Nat -> Set
Admissible values =
  Nonempty values
  and
  All Positive values
  and
  sumList values == 1979

putnam-1979-a1 : Set
putnam-1979-a1 =
  Admissible putnam-1979-a1-solution
  and
  ((values : List Nat) ->
    Admissible values ->
    productList values <= productList putnam-1979-a1-solution)
