-- Statement-only formalization of PutnamBench corpus artifact putnam_2024_a3
-- (putnambench__agda__putnam_2024_a3): among increasing bijective 3 by 2024
-- tableaux, some pair of positions is ordered in between one third and two
-- thirds of all tableaux. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2024A3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<F_ _<=N_
infixr 3 _and_

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data _<F_ : {n : Nat} -> Fin n -> Fin n -> Set where
  fzero<fsuc :
    {n : Nat} {j : Fin n} ->
    fzero <F fsuc j
  fsuc<fsuc :
    {n : Nat} {i j : Fin n} ->
    i <F j ->
    fsuc i <F fsuc j

Row : Set
Row =
  Fin 3

Column : Set
Column =
  Fin 2024

Value : Set
Value =
  Fin 6072

Grid : Set
Grid =
  Row -> Column -> Value

record Position : Set where
  constructor position
  field
    row    : Row
    column : Column

open Position

record IsBijection (tableau : Grid) : Set where
  field
    inverse : Value -> Position
    inverse-entry-row :
      (i : Row) ->
      (j : Column) ->
      row (inverse (tableau i j)) == i
    inverse-entry-column :
      (i : Row) ->
      (j : Column) ->
      column (inverse (tableau i j)) == j
    entry-inverse :
      (value : Value) ->
      tableau
        (row (inverse value))
        (column (inverse value)) == value

record Admissible (tableau : Grid) : Set where
  field
    bijective :
      IsBijection tableau
    columns-strictly-increasing :
      (j : Column) ->
      (i k : Row) ->
      i <F k ->
      tableau i j <F tableau k j
    rows-strictly-increasing :
      (i : Row) ->
      (j l : Column) ->
      j <F l ->
      tableau i j <F tableau i l

GridEqual : Grid -> Grid -> Set
GridEqual left right =
  (i : Row) ->
  (j : Column) ->
  left i j == right i j

record HasGridCardinality
  (member : Grid -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      Grid
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (tableau : Grid) ->
      member tableau ->
      Exists (Fin cardinality)
        (\ index ->
          GridEqual tableau (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      GridEqual
        (enumerate left-index)
        (enumerate right-index) ->
      left-index == right-index

Favorable :
  Row ->
  Column ->
  Row ->
  Column ->
  Grid ->
  Set
Favorable a b c d tableau =
  Admissible tableau
  and
  tableau a b <F tableau c d

putnam-2024-a3 : Set
putnam-2024-a3 =
  Exists Row
    (\ a ->
      Exists Column
        (\ b ->
          Exists Row
            (\ c ->
              Exists Column
                (\ d ->
                  Exists Nat
                    (\ total-predecessor ->
                      HasGridCardinality
                        Admissible
                        (suc total-predecessor)
                      and
                      Exists Nat
                        (\ favorable-count ->
                          HasGridCardinality
                            (Favorable a b c d)
                            favorable-count
                          and
                          ((suc total-predecessor <=N
                              3 * favorable-count)
                            and
                            (3 * favorable-count <=N
                              2 * suc total-predecessor))))))))
