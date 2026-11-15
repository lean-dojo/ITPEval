-- Statement-only formalization of PutnamBench corpus artifact putnam_1989_b2:
-- every nonempty associative left- and right-cancellative semigroup in which
-- each element has only finitely many positive powers is a group.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Member {A : Set} (x : A) : List A -> Set where
  at-head : {xs : List A} -> Member x (x ∷ xs)
  in-tail :
    {y : A} ->
    {xs : List A} ->
    Member x xs ->
    Member x (y ∷ xs)

record Nonempty (A : Set) : Set where
  field
    element : A

record Semigroup (S : Set) : Set where
  field
    multiply : S -> S -> S
    associative :
      (x y z : S) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)

open Semigroup

record Cancellative
  {S : Set}
  (algebra : Semigroup S) :
  Set where

  field
    left-cancel :
      (x y z : S) ->
      multiply algebra x y == multiply algebra x z ->
      y == z
    right-cancel :
      (x y z : S) ->
      multiply algebra y x == multiply algebra z x ->
      y == z

positivePower :
  {S : Set} ->
  Semigroup S ->
  S ->
  Nat ->
  S
positivePower algebra a zero =
  a
positivePower algebra a (suc n) =
  multiply algebra a (positivePower algebra a n)

FiniteImage :
  {A B : Set} ->
  (A -> B) ->
  Set
FiniteImage {A} {B} function =
  Exists (List B)
    (\ values ->
      (x : A) ->
      Member (function x) values)

record IsGroup
  {S : Set}
  (algebra : Semigroup S) :
  Set where

  field
    identity : S
    left-identity :
      (x : S) ->
      multiply algebra identity x == x
    right-identity :
      (x : S) ->
      multiply algebra x identity == x
    inverse :
      (x : S) ->
      Exists S
        (\ y ->
          Both
            (multiply algebra x y == identity)
            (multiply algebra y x == identity))

putnam-1989-b2 : Set1
putnam-1989-b2 =
  (S : Set) ->
  Nonempty S ->
  (algebra : Semigroup S) ->
  Cancellative algebra ->
  ((a : S) -> FiniteImage (positivePower algebra a)) ->
  IsGroup algebra
