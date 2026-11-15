-- Statement-only formalization of PutnamBench corpus artifact putnam_2012_b3
-- (putnambench__agda__putnam_2012_b3): every round-robin tournament on 2n
-- teams admits an injective choice of one winning team from each day.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2012B3 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_
infixr 3 _and_

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

pred : Nat -> Nat
pred zero =
  zero
pred (suc n) =
  n

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

Team : Nat -> Set
Team n =
  Fin (two * n)

Day : Nat -> Set
Day n =
  Fin (pred (two * n))

Matchups : Nat -> Set
Matchups n =
  Day n -> Team n -> Team n

Wins : Nat -> Set
Wins n =
  Day n -> Team n -> Bool

notBool : Bool -> Bool
notBool false =
  true
notBool true =
  false

DailyPerfectMatchings :
  {n : Nat} ->
  Matchups n ->
  Set
DailyPerfectMatchings {n} matchups =
  (d : Day n) ->
  (team : Team n) ->
  matchups d team != team
  and
  matchups d (matchups d team) == team

EveryPairMeets :
  {n : Nat} ->
  Matchups n ->
  Set
EveryPairMeets {n} matchups =
  (first-team second-team : Team n) ->
  first-team != second-team ->
  Exists (Day n)
    (\ d -> matchups d first-team == second-team)

ResultsAreOpposite :
  {n : Nat} ->
  Matchups n ->
  Wins n ->
  Set
ResultsAreOpposite {n} matchups wins =
  (d : Day n) ->
  (team : Team n) ->
  wins d team == notBool (wins d (matchups d team))

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective {A} function =
  (x y : A) ->
  function x == function y ->
  x == y

WinningChoice :
  {n : Nat} ->
  Wins n ->
  Set
WinningChoice {n} wins =
  Exists (Day n -> Team n)
    (\ choices ->
      ((d : Day n) -> wins d (choices d) == true)
      and
      Injective choices)

putnam-2012-b3 : Set
putnam-2012-b3 =
  (n : Nat) ->
  Positive n ->
  (matchups : Matchups n) ->
  (wins : Wins n) ->
  DailyPerfectMatchings {n} matchups ->
  EveryPairMeets {n} matchups ->
  ResultsAreOpposite {n} matchups wins ->
  WinningChoice {n} wins
