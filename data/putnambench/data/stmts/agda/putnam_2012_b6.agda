-- Statement-only formalization of PutnamBench corpus artifact putnam_2012_b6:
-- the cubic permutation of residue classes modulo an odd prime p congruent to
-- 2 modulo 3 is even exactly when p is congruent to 3 modulo 4. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2012B6 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _!=_ _<=N_ _divides_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

data Bottom : Set where

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

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record Pair (A B : Set) : Set where
  constructor pair
  field
    first-coordinate  : A
    second-coordinate : B

open Pair

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : dividend == divisor * quotient

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc i) =
  suc (toNat i)

finEqual : {n : Nat} -> Fin n -> Fin n -> Bool
finEqual fzero fzero =
  true
finEqual fzero (fsuc j) =
  false
finEqual (fsuc i) fzero =
  false
finEqual (fsuc i) (fsuc j) =
  finEqual i j

swap :
  {n : Nat} ->
  Fin n ->
  Fin n ->
  Fin n ->
  Fin n
swap left-index right-index index with finEqual index left-index
... | true =
  right-index
... | false with finEqual index right-index
...   | true =
  left-index
...   | false =
  index

applyTranspositions :
  {n count : Nat} ->
  (Fin count -> Pair (Fin n) (Fin n)) ->
  Fin n ->
  Fin n
applyTranspositions {count = zero} transpositions index =
  index
applyTranspositions {count = suc count} transpositions index =
  applyTranspositions
    (\ i -> transpositions (fsuc i))
    (swap
      (first-coordinate (transpositions fzero))
      (second-coordinate (transpositions fzero))
      index)

PointwiseEqual :
  {n : Nat} ->
  (Fin n -> Fin n) ->
  (Fin n -> Fin n) ->
  Set
PointwiseEqual left-function right-function =
  (index : _) ->
  left-function index == right-function index

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective function =
  (x y : _) ->
  function x == function y ->
  x == y

Surjective :
  {A B : Set} ->
  (A -> B) ->
  Set
Surjective {A} {B} function =
  (y : B) ->
  Exists A
    (\ x -> function x == y)

IsPermutation :
  {n : Nat} ->
  (Fin n -> Fin n) ->
  Set
IsPermutation permutation =
  Injective permutation
  and
  Surjective permutation

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

record Odd (n : Nat) : Set where
  field
    half : Nat
    odd-equation : n == two * half + one

record Prime (p : Nat) : Set where
  field
    at-least-two : two <=N p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == one) or (d == p)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus left-value right-value =
  naturalMod left-value modulus == naturalMod right-value modulus

CubicPermutation :
  {p : Nat} ->
  (Fin p -> Fin p) ->
  Set
CubicPermutation {p} permutation =
  IsPermutation permutation
  and
  ((index : Fin p) ->
    toNat (permutation index)
    ==
    naturalMod
      (toNat index * toNat index * toNat index)
      p)

EvenPermutation :
  {n : Nat} ->
  (Fin n -> Fin n) ->
  Set
EvenPermutation {n} permutation =
  Exists Nat
    (\ half-length ->
      Exists (Fin (two * half-length) -> Pair (Fin n) (Fin n))
        (\ transpositions ->
          ((index : Fin (two * half-length)) ->
            first-coordinate (transpositions index)
            !=
            second-coordinate (transpositions index))
          and
          PointwiseEqual
            permutation
            (applyTranspositions transpositions)))

putnam-2012-b6 : Set
putnam-2012-b6 =
  (p : Nat) ->
  Odd p ->
  Prime p ->
  ModEq three p two ->
  (permutation : Fin p -> Fin p) ->
  CubicPermutation permutation ->
  EvenPermutation permutation
  iff
  ModEq four p three
