-- Statement-only formalization of PutnamBench corpus artifact putnam_2004_a5
-- (putnambench__agda__putnam_2004_a5): the expected number of connected
-- monochromatic regions in a uniformly two-colored finite checkerboard is
-- greater than one eighth of the number of squares. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2004A5 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<N_
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

record Inhabited (A : Set) : Set where
  constructor inhabitant
  field
    element : A

data _<N_ : Nat -> Nat -> Set where
  zero<sucN : {n : Nat} -> zero <N suc n
  suc<sucN  : {m n : Nat} -> m <N n -> suc m <N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

weaken : {n : Nat} -> Fin n -> Fin (suc n)
weaken {suc n} fzero =
  fzero
weaken {suc n} (fsuc i) =
  fsuc (weaken i)

record Cell (m n : Nat) : Set where
  constructor cell
  field
    row    : Fin m
    column : Fin n

data Neighbor : {n : Nat} -> Fin n -> Fin n -> Set where
  forward :
    {n : Nat} {i : Fin n} ->
    Neighbor (weaken i) (fsuc i)
  backward :
    {n : Nat} {i : Fin n} ->
    Neighbor (fsuc i) (weaken i)

Adjacent :
  {m n : Nat} ->
  Cell m n ->
  Cell m n ->
  Set
Adjacent (cell a b) (cell c d) =
  ((a == c) and Neighbor b d)
  or
  ((b == d) and Neighbor a c)

Coloring : Nat -> Nat -> Set
Coloring m n =
  Fin m -> Fin n -> Bool

colorAt :
  {m n : Nat} ->
  Coloring m n ->
  Cell m n ->
  Bool
colorAt coloring (cell i j) =
  coloring i j

data MonochromaticPath
  {m n : Nat}
  (coloring : Coloring m n)
  (color : Bool) :
  Cell m n ->
  Cell m n ->
  Set where

  singleton :
    {P : Cell m n} ->
    colorAt coloring P == color ->
    MonochromaticPath coloring color P P

  extend :
    {P Q R : Cell m n} ->
    colorAt coloring P == color ->
    Adjacent P Q ->
    MonochromaticPath coloring color Q R ->
    MonochromaticPath coloring color P R

Connected :
  {m n : Nat} ->
  Coloring m n ->
  Cell m n ->
  Cell m n ->
  Set
Connected coloring P Q =
  Exists Bool
    (\ color -> MonochromaticPath coloring color P Q)

record ComponentCount
  {m n : Nat}
  (coloring : Coloring m n)
  (count : Nat) :
  Set where

  field
    representative :
      Fin count ->
      Cell m n

    every-cell-covered :
      (P : Cell m n) ->
      Exists (Fin count)
        (\ index ->
          Connected coloring P (representative index))

    representatives-unique :
      (left-index right-index : Fin count) ->
      Connected coloring
        (representative left-index)
        (representative right-index) ->
      left-index == right-index

prepend :
  {n : Nat} ->
  Bool ->
  (Fin n -> Bool) ->
  Fin (suc n) ->
  Bool
prepend head tail fzero =
  head
prepend head tail (fsuc i) =
  tail i

sumBoolFunctions :
  {n : Nat} ->
  ((Fin n -> Bool) -> Nat) ->
  Nat
sumBoolFunctions {zero} term =
  term (\ ())
sumBoolFunctions {suc n} term =
  sumBoolFunctions
    (\ tail -> term (prepend false tail))
  +
  sumBoolFunctions
    (\ tail -> term (prepend true tail))

prependRow :
  {m n : Nat} ->
  (Fin n -> Bool) ->
  Coloring m n ->
  Coloring (suc m) n
prependRow row rest fzero j =
  row j
prependRow row rest (fsuc i) j =
  rest i j

sumColorings :
  {m n : Nat} ->
  (Coloring m n -> Nat) ->
  Nat
sumColorings {zero} {n} term =
  term (\ ())
sumColorings {suc m} {n} term =
  sumBoolFunctions
    (\ row ->
      sumColorings
        (\ rest ->
          term (prependRow row rest)))

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

eight : Nat
eight =
  8

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

putnam-2004-a5 : Set
putnam-2004-a5 =
  (m n : Nat) ->
  Inhabited (Cell m n) ->
  (cmr : Coloring m n -> Nat) ->
  ((coloring : Coloring m n) ->
    ComponentCount coloring (cmr coloring)) ->
  (power two (m * n) * (m * n))
  <N
  (eight * sumColorings cmr)
