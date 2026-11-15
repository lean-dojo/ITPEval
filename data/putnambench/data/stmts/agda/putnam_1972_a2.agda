-- Statement-only formalization of PutnamBench corpus artifact putnam_1972_a2:
-- binary operations satisfying the two involutive identities are commutative,
-- but such an operation need not be associative. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)

infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

Identities :
  {A : Set} ->
  (A -> A -> A) ->
  Set
Identities operation =
  (x y : _) ->
  (operation x (operation x y) == y)
  and
  (operation (operation y x) x == y)

Associative :
  {A : Set} ->
  (A -> A -> A) ->
  Set
Associative operation =
  (x y z : _) ->
  operation x (operation y z) ==
  operation (operation x y) z

record NonAssociativeExample : Set1 where
  field
    Carrier  : Set
    operation : Carrier -> Carrier -> Carrier
    identities : Identities operation
    not-associative : Not (Associative operation)

record Putnam1972A2 : Set1 where
  field
    commutativity :
      (A : Set) ->
      (operation : A -> A -> A) ->
      Identities operation ->
      (x y : A) ->
      operation x y == operation y x
    nonassociative-example :
      NonAssociativeExample

putnam-1972-a2 : Set1
putnam-1972-a2 =
  Putnam1972A2
