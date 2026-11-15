-- Statement-only formalization of PutnamBench corpus artifact putnam_1984_b3:
-- every finite set with at least two elements admits a right-cancellative
-- binary operation that is nonassociative at every triple. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_
infixr 3 _and_

data Bottom : Set where

record Top : Set where
  constructor truth

Not :
  {level : Level} ->
  Set level ->
  Set level
Not A =
  A -> Bottom

_!=_ :
  {level : Level} ->
  {A : Set level} ->
  A ->
  A ->
  Set level
x != y =
  Not (x == y)

record _and_
  {left-level right-level : Level}
  (A : Set left-level)
  (B : Set right-level) :
  Set (left-level ⊔ right-level) where

  constructor both
  field
    first  : A
    second : B

record Iff
  {left-level right-level : Level}
  (A : Set left-level)
  (B : Set right-level) :
  Set (left-level ⊔ right-level) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {value-level property-level : Level}
  (A : Set value-level)
  (property : A -> Set property-level) :
  Set (value-level ⊔ property-level) where

  constructor witness
  field
    value     : A
    satisfies : property value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Finite
  {level : Level}
  (A : Set level) :
  Set level where

  field
    cardinality : Nat
    toFin        : A -> Fin cardinality
    fromFin      : Fin cardinality -> A
    from-to      : (x : A) -> fromFin (toFin x) == x
    to-from      : (i : Fin cardinality) -> toFin (fromFin i) == i

open Finite

two : Nat
two =
  suc (suc zero)

AtLeastTwo :
  {level : Level} ->
  {A : Set level} ->
  Finite A ->
  Set
AtLeastTwo finite =
  two <=N cardinality finite

OperationLaws :
  {level : Level} ->
  {A : Set level} ->
  (A -> A -> A) ->
  Set level
OperationLaws multiply =
  (x y z : _) ->
  (multiply x z == multiply y z -> x == y)
  and
  multiply x (multiply y z) != multiply (multiply x y) z

UniversalClaim :
  (level : Level) ->
  Set (lsuc level)
UniversalClaim level =
  (F : Set level) ->
  (finite : Finite F) ->
  AtLeastTwo finite ->
  Exists (F -> F -> F) OperationLaws

putnam-1984-b3-solution : Set
putnam-1984-b3-solution =
  Top

putnam-1984-b3 :
  {level : Level} ->
  Set (lsuc level)
putnam-1984-b3 {level} =
  Iff
    (UniversalClaim level)
    putnam-1984-b3-solution
