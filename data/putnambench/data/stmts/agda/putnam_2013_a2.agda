-- Statement-only formalization of PutnamBench corpus artifact putnam_2013_a2
-- (putnambench__agda__putnam_2013_a2): the minimum possible final entry in
-- each increasing integer sequence making a positive nonsquare times its
-- product a square defines an injective function. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2013A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_ _<=N_ _<=Z_ _<Z_
infixr 3 _and_

data Bottom : Set where

record Top : Set where
  constructor truth

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data _<=Z_ : Int -> Int -> Set where
  negative<=positive :
    {m n : Nat} ->
    negsuc m <=Z pos n
  positive<=positive :
    {m n : Nat} ->
    m <=N n ->
    pos m <=Z pos n
  negative<=negative :
    {m n : Nat} ->
    n <=N m ->
    negsuc m <=Z negsuc n

_<Z_ : Int -> Int -> Set
x <Z y =
  (x <=Z y) and (x != y)

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

oneZ : Int
oneZ =
  pos (suc zero)

product : List Int -> Int
product [] =
  oneZ
product (x ∷ xs) =
  multiplyInt x (product xs)

StrictlyIncreasing : List Int -> Set
StrictlyIncreasing [] =
  Top
StrictlyIncreasing (_ ∷ []) =
  Top
StrictlyIncreasing (x ∷ y ∷ xs) =
  (x <Z y) and StrictlyIncreasing (y ∷ xs)

LastIs : List Int -> Int -> Set
LastIs [] last =
  Bottom
LastIs (x ∷ []) last =
  x == last
LastIs (_ ∷ y ∷ xs) last =
  LastIs (y ∷ xs) last

PositiveNonSquare : Int -> Set
PositiveNonSquare n =
  ((pos zero) <Z n)
  and
  Not
    (Exists Int
      (\ m ->
        multiplyInt m m == n))

Admissible : Int -> List Int -> Set
Admissible n [] =
  Bottom
Admissible n (a ∷ as) =
  (n <Z a)
  and
  (Exists Int
    (\ m ->
      multiplyInt m m ==
        multiplyInt n (product (a ∷ as))))
  and
  StrictlyIncreasing (a ∷ as)

TerminalValue : Int -> Int -> Set
TerminalValue n last =
  Exists (List Int)
    (\ choices ->
      Admissible n choices
      and
      LastIs choices last)

IsMinimumTerminal : (Int -> Int) -> Int -> Set
IsMinimumTerminal f n =
  TerminalValue n (f n)
  and
  ((last : Int) ->
    TerminalValue n last ->
    f n <=Z last)

InjectiveOnPositiveNonSquares : (Int -> Int) -> Set
InjectiveOnPositiveNonSquares f =
  (x y : Int) ->
  PositiveNonSquare x ->
  PositiveNonSquare y ->
  f x == f y ->
  x == y

putnam-2013-a2 : Set
putnam-2013-a2 =
  (f : Int -> Int) ->
  ((n : Int) ->
    PositiveNonSquare n ->
    IsMinimumTerminal f n) ->
  InjectiveOnPositiveNonSquares f
