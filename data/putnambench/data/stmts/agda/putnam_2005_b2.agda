-- Statement-only formalization of PutnamBench corpus artifact putnam_2005_b2
-- (putnambench__agda__putnam_2005_b2): the positive integer tuples whose
-- sum is 5n - 4 and whose reciprocal sum is one. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2005B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=N_
infixr 5 _::_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor top

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

five : Nat
five =
  suc four

six : Nat
six =
  suc five

Positive : Nat -> Set
Positive n =
  one <=N n

AllPositive : {n : Nat} -> Vec Nat n -> Set
AllPositive [] =
  Top
AllPositive (x :: xs) =
  Positive x and AllPositive xs

sum : {n : Nat} -> Vec Nat n -> Nat
sum [] =
  zero
sum (x :: xs) =
  x + sum xs

product : {n : Nat} -> Vec Nat n -> Nat
product [] =
  one
product (x :: xs) =
  x * product xs

reciprocalNumerator : {n : Nat} -> Vec Nat n -> Nat
reciprocalNumerator [] =
  zero
reciprocalNumerator (x :: xs) =
  product xs + x * reciprocalNumerator xs

SatisfiesEquations :
  (n : Nat) ->
  Vec Nat n ->
  Set
SatisfiesEquations n k =
  Positive n
  and
  AllPositive k
  and
  sum k == five * n - four
  and
  reciprocalNumerator k == product k

Solution : {n : Nat} -> Vec Nat n -> Set
Solution [] =
  Bottom
Solution (a :: []) =
  a == one
Solution (a :: b :: []) =
  Bottom
Solution (a :: b :: c :: []) =
  (a == two and b == three and c == six)
  or
  (a == two and b == six and c == three)
  or
  (a == three and b == two and c == six)
  or
  (a == three and b == six and c == two)
  or
  (a == six and b == two and c == three)
  or
  (a == six and b == three and c == two)
Solution (a :: b :: c :: d :: []) =
  a == four
  and
  b == four
  and
  c == four
  and
  d == four
Solution (a :: b :: c :: d :: e :: rest) =
  Bottom

putnam-2005-b2 : Set
putnam-2005-b2 =
  (n : Nat) ->
  (k : Vec Nat n) ->
  Iff
    (SatisfiesEquations n k)
    (Solution k)
