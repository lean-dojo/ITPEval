-- Statement-only formalization of PutnamBench corpus artifact putnam_2025_a3
-- (putnambench__agda__putnam_2025_a3): Alice has no winning strategy in the
-- non-repeating ternary-string game for any positive string length. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2025A3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_
infixr 5 _::_
infixr 4 _++_
infixr 3 _and_
infixr 2 _or_

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

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record ExistsUnique (A : Set) (P : A -> Set) : Set where
  constructor unique-witness
  field
    value    : A
    property : P value
    unique   : (other : A) -> P other -> other == value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finValue : {n : Nat} -> Fin n -> Nat
finValue fzero =
  zero
finValue (fsuc index) =
  suc (finValue index)

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ suffix =
  suffix
(head :: tail) ++ suffix =
  head :: (tail ++ suffix)

data MemberBy {A : Set}
  (equivalent : A -> A -> Set)
  (item : A) :
  List A -> Set where

  member-here :
    {head : A} {tail : List A} ->
    equivalent item head ->
    MemberBy equivalent item (head :: tail)

  member-there :
    {head : A} {tail : List A} ->
    MemberBy equivalent item tail ->
    MemberBy equivalent item (head :: tail)

data NoDuplicatesBy {A : Set}
  (equivalent : A -> A -> Set) :
  List A -> Set where

  no-duplicates-empty :
    NoDuplicatesBy equivalent []

  no-duplicates-cons :
    {head : A} {tail : List A} ->
    Not (MemberBy equivalent head tail) ->
    NoDuplicatesBy equivalent tail ->
    NoDuplicatesBy equivalent (head :: tail)

one : Nat
one =
  suc zero

three : Nat
three =
  suc (suc (suc zero))

GameString : Nat -> Set
GameString n =
  Fin n -> Fin three

SameGameString :
  {n : Nat} ->
  GameString n ->
  GameString n ->
  Set
SameGameString {n} left-string right-string =
  (index : Fin n) ->
  left-string index == right-string index

initialState : (n : Nat) -> GameString n
initialState n index =
  fzero

isValidMove :
  {n : Nat} ->
  GameString n ->
  GameString n ->
  Set
isValidMove {n} before after =
  ExistsUnique (Fin n)
    (\ index -> before index != after index)
  and
  ((index : Fin n) ->
    before index != after index ->
    (suc (finValue (before index)) == finValue (after index))
    or
    (suc (finValue (after index)) == finValue (before index)))

data ChainFrom {A : Set} (relation : A -> A -> Set) :
  A -> List A -> Set where

  chain-empty :
    {start : A} ->
    ChainFrom relation start []

  chain-cons :
    {start next : A} {tail : List A} ->
    relation start next ->
    ChainFrom relation next tail ->
    ChainFrom relation start (next :: tail)

IsValidGamePlay :
  {n : Nat} ->
  List (GameString n) ->
  Set
IsValidGamePlay {n} play =
  ChainFrom isValidMove (initialState n) play
  and
  NoDuplicatesBy SameGameString (initialState n :: play)

data HasWinningStrategy (n : Nat) :
  List (GameString n) -> Set where

  winning-move :
    (play : List (GameString n)) ->
    (move : GameString n) ->
    IsValidGamePlay (play ++ (move :: [])) ->
    ((reply : GameString n) ->
      IsValidGamePlay (play ++ (move :: reply :: [])) ->
      HasWinningStrategy n (play ++ (move :: reply :: []))) ->
    HasWinningStrategy n play

AliceHasWinningStrategy : Nat -> Set
AliceHasWinningStrategy n =
  HasWinningStrategy n []

putnam-2025-a3-solution : Nat -> Set
putnam-2025-a3-solution n =
  Bottom

putnam-2025-a3 : Set
putnam-2025-a3 =
  (n : Nat) ->
  one <=N n ->
  Iff
    (putnam-2025-a3-solution n)
    (AliceHasWinningStrategy n)
