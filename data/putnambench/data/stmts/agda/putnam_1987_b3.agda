-- Statement-only formalization of PutnamBench corpus artifact putnam_1987_b3:
-- the unit circle over any field of characteristic not two is exactly the
-- singleton (1, 0) together with its standard rational parametrization.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)

infix 4 _!=_
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

record Field (F : Set) : Set1 where
  field
    zeroF oneF : F
    add multiply : F -> F -> F
    negate inverse : F -> F

    one-not-zero :
      oneF != zeroF

    add-commutative :
      (x y : F) ->
      add x y == add y x
    add-associative :
      (x y z : F) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : F) ->
      add x zeroF == x
    add-inverse :
      (x : F) ->
      add x (negate x) == zeroF

    multiply-commutative :
      (x y : F) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : F) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : F) ->
      multiply x oneF == x
    multiply-zero :
      (x : F) ->
      multiply x zeroF == zeroF
    distribute :
      (x y z : F) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)

    inverse-zero :
      inverse zeroF == zeroF
    multiply-inverse :
      (x : F) ->
      x != zeroF ->
      multiply x (inverse x) == oneF

open Field

square :
  {F : Set} ->
  Field F ->
  F ->
  F
square algebra x =
  multiply algebra x x

subtract :
  {F : Set} ->
  Field F ->
  F ->
  F ->
  F
subtract algebra x y =
  add algebra x (negate algebra y)

divide :
  {F : Set} ->
  Field F ->
  F ->
  F ->
  F
divide algebra x y =
  multiply algebra x (inverse algebra y)

module Putnam1987B3Statement
  {F : Set}
  (algebra : Field F) where

  two : F
  two =
    add algebra (oneF algebra) (oneF algebra)

  UnitCircle : F -> F -> Set
  UnitCircle x y =
    add algebra
      (square algebra x)
      (square algebra y)
    ==
    oneF algebra

  EligibleParameter : F -> Set
  EligibleParameter r =
    square algebra r != negate algebra (oneF algebra)

  parameterX : F -> F
  parameterX r =
    divide algebra
      (subtract algebra
        (square algebra r)
        (oneF algebra))
      (add algebra
        (square algebra r)
        (oneF algebra))

  parameterY : F -> F
  parameterY r =
    divide algebra
      (multiply algebra two r)
      (add algebra
        (square algebra r)
        (oneF algebra))

  ParametrizedPoint : F -> F -> Set
  ParametrizedPoint x y =
    Exists F
      (\ r ->
        EligibleParameter r
        and
        x == parameterX r
        and
        y == parameterY r)

  ListedPoint : F -> F -> Set
  ListedPoint x y =
    (x == oneF algebra and y == zeroF algebra)
    or
    ParametrizedPoint x y

  proposition : Set
  proposition =
    (x y : F) ->
    UnitCircle x y iff ListedPoint x y

putnam-1987-b3 : Set1
putnam-1987-b3 =
  (F : Set) ->
  (algebra : Field F) ->
  add algebra (oneF algebra) (oneF algebra) != zeroF algebra ->
  Putnam1987B3Statement.proposition algebra
