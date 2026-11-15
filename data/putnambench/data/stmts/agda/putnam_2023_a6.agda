-- Statement-only formalization of PutnamBench corpus artifact putnam_2023_a6
-- (putnambench__agda__putnam_2023_a6): Bob has a winning parity strategy
-- in the alternating permutation game for every positive board size.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2023A6 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=N_ _<N_ _member_
infixr 3 _and_
infix 1 _iff_
infixr 5 _++_

data Bottom : Set where

data Top : Set where
  trivial : Top

Not : Set -> Set
Not A =
  A -> Bottom

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

oneN : Nat
oneN =
  suc zero

Positive : Nat -> Set
Positive n =
  oneN <=N n

InRange : Nat -> Nat -> Set
InRange n value =
  oneN <=N value and value <=N n

data _member_ {A : Set} (x : A) : List A -> Set where
  here :
    {xs : List A} ->
    x member (x ∷ xs)
  there :
    {y : A} ->
    {xs : List A} ->
    x member xs ->
    x member (y ∷ xs)

Distinct : {A : Set} -> List A -> Set
Distinct [] =
  Top
Distinct (x ∷ xs) =
  Not (x member xs) and Distinct xs

AllInRange : Nat -> List Nat -> Set
AllInRange n [] =
  Top
AllInRange n (x ∷ xs) =
  InRange n x and AllInRange n xs

length : {A : Set} -> List A -> Nat
length [] =
  zero
length (x ∷ xs) =
  suc (length xs)

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys =
  ys
(x ∷ xs) ++ ys =
  x ∷ (xs ++ ys)

PartialGame : Nat -> List Nat -> Set
PartialGame n moves =
  Distinct moves and AllInRange n moves

ValidGame : Nat -> List Nat -> Set
ValidGame n moves =
  length moves == n and PartialGame n moves

data Parity : Set where
  even odd : Parity

toggle : Parity -> Parity
toggle even =
  odd
toggle odd =
  even

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc n) =
  false
natEqual (suc m) zero =
  false
natEqual (suc m) (suc n) =
  natEqual m n

fixedPointParityFrom : Nat -> List Nat -> Parity
fixedPointParityFrom index [] =
  even
fixedPointParityFrom index (value ∷ values)
  with natEqual value (suc index)
... | true =
  toggle (fixedPointParityFrom (suc index) values)
... | false =
  fixedPointParityFrom (suc index) values

fixedPointParity : List Nat -> Parity
fixedPointParity =
  fixedPointParityFrom zero

Strategy : Set
Strategy =
  List Nat -> Nat

data Turn : Set where
  alice bob : Turn

nextTurn : Turn -> Turn
nextTurn alice =
  bob
nextTurn bob =
  alice

MoveCondition :
  Turn ->
  Strategy ->
  List Nat ->
  Nat ->
  Set
MoveCondition alice strategy prefix value =
  Top
MoveCondition bob strategy prefix value =
  value == strategy prefix

ConformsFrom :
  Turn ->
  List Nat ->
  List Nat ->
  Strategy ->
  Set
ConformsFrom turn prefix [] strategy =
  Top
ConformsFrom turn prefix (value ∷ values) strategy =
  MoveCondition turn strategy prefix value
  and
  ConformsFrom
    (nextTurn turn)
    (prefix ++ (value ∷ []))
    values
    strategy

ConformsToStrategy : List Nat -> Strategy -> Set
ConformsToStrategy moves strategy =
  ConformsFrom alice [] moves strategy

BobTurnAfter : Nat -> Set
BobTurnAfter zero =
  Bottom
BobTurnAfter (suc zero) =
  Top
BobTurnAfter (suc (suc n)) =
  BobTurnAfter n

ValidStrategy : Nat -> Strategy -> Set
ValidStrategy n strategy =
  (prefix : List Nat) ->
  PartialGame n prefix ->
  length prefix <N n ->
  BobTurnAfter (length prefix) ->
  InRange n (strategy prefix)
  and
  Not (strategy prefix member prefix)

WinsWithGoal : Nat -> Parity -> Strategy -> Set
WinsWithGoal n goal strategy =
  ValidStrategy n strategy
  and
  ((moves : List Nat) ->
    ValidGame n moves ->
    ConformsToStrategy moves strategy ->
    fixedPointParity moves == goal)

BobHasWinningStrategy : Nat -> Set
BobHasWinningStrategy n =
  Exists Parity
    (\ goal ->
      Exists Strategy
        (\ strategy ->
          WinsWithGoal n goal strategy))

WinningSize : Nat -> Set
WinningSize n =
  Positive n and BobHasWinningStrategy n

SolutionSize : Nat -> Set
SolutionSize n =
  Positive n

putnam-2023-a6 : Set
putnam-2023-a6 =
  (n : Nat) ->
  WinningSize n iff SolutionSize n
