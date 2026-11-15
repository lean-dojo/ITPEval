-- Statement-only formalization of Hundred Theorems item 031, "Ramsey's Theorem":
-- every finite coloring of the fixed-cardinality finite subsets of an infinite
-- set has an infinite monochromatic subset. This file contains no proof.

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<_ _is-subset-of_
infixr 5 _::_

data Bottom : Set where

Not : {level : Level} -> Set level -> Set level
Not proposition = proposition -> Bottom

data _<_ : Nat -> Nat -> Set where
  zero-less-successor :
    {n : Nat} ->
    zero < suc n
  successor-less-successor :
    {m n : Nat} ->
    m < n ->
    suc m < suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

lookup :
  {A : Set} ->
  {n : Nat} ->
  Vec A n ->
  Fin n ->
  A
lookup [] ()
lookup (x :: xs) fzero = x
lookup (x :: xs) (fsuc i) = lookup xs i

Subset : Set -> Set1
Subset A = A -> Set

_is-subset-of_ :
  {A : Set} ->
  Subset A ->
  Subset A ->
  Set
_is-subset-of_ {A} X Y =
  (x : A) ->
  X x ->
  Y x

record SameSubset
  {A : Set}
  (X Y : Subset A) :
  Set1 where

  field
    forward : X is-subset-of Y
    backward : Y is-subset-of X

record OccursAt
  {A : Set}
  {n : Nat}
  (elements : Vec A n)
  (x : A) :
  Set where

  field
    index : Fin n
    equality : lookup elements index == x

record HasCardinality
  {A : Set}
  (X : Subset A)
  (n : Nat) :
  Set1 where

  field
    elements : Vec A n
    listed-elements-belong :
      (i : Fin n) ->
      X (lookup elements i)
    every-element-is-listed :
      (x : A) ->
      X x ->
      OccursAt elements x
    no-repetitions :
      (i j : Fin n) ->
      lookup elements i == lookup elements j ->
      i == j

record Finite
  {A : Set}
  (X : Subset A) :
  Set1 where

  field
    cardinality : Nat
    has-cardinality : HasCardinality X cardinality

Infinite :
  {A : Set} ->
  Subset A ->
  Set1
Infinite X =
  Not (Finite X)

ExtensionalColoring :
  {A : Set} ->
  (Subset A -> Nat) ->
  Set1
ExtensionalColoring coloring =
  (X Y : Subset _) ->
  SameSubset X Y ->
  coloring X == coloring Y

BoundedColoringOn :
  {A : Set} ->
  Subset A ->
  Nat ->
  Nat ->
  (Subset A -> Nat) ->
  Set1
BoundedColoringOn {A} S subset-size color-count coloring =
  (X : Subset A) ->
  X is-subset-of S ->
  HasCardinality X subset-size ->
  coloring X < color-count

record RamseyConclusion
  {A : Set}
  (S : Subset A)
  (subset-size color-count : Nat)
  (coloring : Subset A -> Nat) :
  Set1 where

  field
    homogeneous-set : Subset A
    contained : homogeneous-set is-subset-of S
    infinite : Infinite homogeneous-set
    homogeneous-color : Nat
    color-in-range : homogeneous-color < color-count
    monochromatic :
      (X : Subset A) ->
      X is-subset-of homogeneous-set ->
      HasCardinality X subset-size ->
      coloring X == homogeneous-color

ramsey-s-theorem : Set1
ramsey-s-theorem =
  (A : Set) ->
  (color-count subset-size : Nat) ->
  (S : Subset A) ->
  (coloring : Subset A -> Nat) ->
  ExtensionalColoring coloring ->
  Infinite S ->
  BoundedColoringOn S subset-size color-count coloring ->
  RamseyConclusion S subset-size color-count coloring
