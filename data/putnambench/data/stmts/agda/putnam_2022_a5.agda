-- Statement-only formalization of PutnamBench corpus artifact putnam_2022_a5
-- (putnambench__agda__putnam_2022_a5): the greatest number of uncovered
-- squares Alice can force in the alternating domino-placement game on a row
-- of 2022 squares is 290. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2022A5 where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=N_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

data Bottom : Set where

Not : {level : Level} -> Set level -> Set level
Not A =
  A -> Bottom

record _and_
  {left-level right-level : Level}
  (A : Set left-level)
  (B : Set right-level) :
  Set (left-level ⊔ right-level) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {left-level right-level : Level}
  (A : Set left-level)
  (B : Set right-level) :
  Set (left-level ⊔ right-level) where

  left  : A -> A or B
  right : B -> A or B

record _iff_
  {left-level right-level : Level}
  (A : Set left-level)
  (B : Set right-level) :
  Set (left-level ⊔ right-level) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {domain-level property-level : Level}
  (A : Set domain-level)
  (P : A -> Set property-level) :
  Set (domain-level ⊔ property-level) where

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

data Even : Nat -> Set where
  even-zero : Even zero
  even-step : {n : Nat} -> Even n -> Even (suc (suc n))

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc index) =
  suc (toNat index)

Square : Set
Square =
  Fin 2022

Board : Set1
Board =
  Square -> Set

Strategy : Set1
Strategy =
  Board -> Board

Game : Set1
Game =
  List Board

EmptyBoard : Board
EmptyBoard square =
  Bottom

SameBoard : Board -> Board -> Set
SameBoard left-board right-board =
  (square : Square) ->
  left-board square iff right-board square

RightNeighbor : Square -> Square -> Set
RightNeighbor left-square right-square =
  (toNat left-square <N 2021)
  and
  (toNat right-square == suc (toNat left-square))

AddDomino :
  Board ->
  Square ->
  Square ->
  Board
AddDomino board left-square right-square square =
  board square
  or
  (square == left-square)
  or
  (square == right-square)

Terminal : Board -> Set
Terminal board =
  (left-square right-square : Square) ->
  RightNeighbor left-square right-square ->
  Not (board left-square) ->
  board right-square

PlacesDomino : Board -> Board -> Set
PlacesDomino before after =
  Exists Square
    (\ left-square ->
      Exists Square
        (\ right-square ->
          RightNeighbor left-square right-square
          and
          Not (before left-square)
          and
          Not (before right-square)
          and
          SameBoard after
            (AddDomino before left-square right-square)))

IsValidMove : Board -> Board -> Set
IsValidMove before after =
  (SameBoard before after and Terminal before)
  or
  PlacesDomino before after

data Chain (relation : Board -> Board -> Set) : Game -> Set1 where
  chain-empty :
    Chain relation []
  chain-singleton :
    {board : Board} ->
    Chain relation (board ∷ [])
  chain-step :
    {first-board second-board : Board}
    {remaining : Game} ->
    relation first-board second-board ->
    Chain relation (second-board ∷ remaining) ->
    Chain relation (first-board ∷ second-board ∷ remaining)

StartsEmpty : Game -> Set
StartsEmpty [] =
  Bottom
StartsEmpty (first-board ∷ remaining) =
  SameBoard first-board EmptyBoard

IsValidGame : Game -> Set1
IsValidGame game =
  StartsEmpty game
  and
  Chain IsValidMove game

data BoardAt : Game -> Nat -> Board -> Set1 where
  at-zero :
    {board : Board}
    {remaining : Game} ->
    BoardAt (board ∷ remaining) zero board
  at-successor :
    {first-board board : Board}
    {remaining : Game}
    {index : Nat} ->
    BoardAt remaining index board ->
    BoardAt (first-board ∷ remaining) (suc index) board

ConformsToStrategy : Game -> Strategy -> Set1
ConformsToStrategy game strategy =
  (index : Nat) ->
  (before after : Board) ->
  BoardAt game index before ->
  BoardAt game (suc index) after ->
  Even index ->
  SameBoard after (strategy before)

record HasCardinality
  (member : Square -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      Square
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (square : Square) ->
      member square ->
      Exists (Fin cardinality)
        (\ index -> square == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

UncoveredAtLeast : Board -> Nat -> Set
UncoveredAtLeast board lower-bound =
  Exists Nat
    (\ uncovered-count ->
      HasCardinality
        (\ square -> Not (board square))
        uncovered-count
      and
      lower-bound <=N uncovered-count)

data LastState : Game -> Board -> Set1 where
  last-singleton :
    {board : Board} ->
    LastState (board ∷ []) board
  last-cons :
    {first-board last-board : Board}
    {remaining : Game} ->
    LastState remaining last-board ->
    LastState (first-board ∷ remaining) last-board

CanEnsure : Nat -> Set1
CanEnsure lower-bound =
  Exists Strategy
    (\ strategy ->
      ((board : Board) ->
        IsValidMove board (strategy board))
      and
      ((game : Game) ->
        IsValidGame game ->
        ConformsToStrategy game strategy ->
        Exists Board
          (\ final-board ->
            LastState game final-board
            and
            UncoveredAtLeast final-board lower-bound)))

record IsGreatest
  {property-level : Level}
  (property : Nat -> Set property-level)
  (greatest : Nat) :
  Set property-level where

  field
    member :
      property greatest
    upper-bound :
      (n : Nat) ->
      property n ->
      n <=N greatest

putnam-2022-a5-solution : Nat
putnam-2022-a5-solution =
  290

putnam-2022-a5 : Set1
putnam-2022-a5 =
  IsGreatest CanEnsure putnam-2022-a5-solution
