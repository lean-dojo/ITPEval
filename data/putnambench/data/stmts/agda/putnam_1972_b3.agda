-- Statement-only formalization of PutnamBench corpus artifact putnam_1972_b3:
-- in an arbitrary group, the relations ABA = BA^2B and A^3 = 1, together
-- with an odd positive power of B equal to 1, imply B = 1.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

record Exists
  {a p : Level}
  (A : Set a)
  (property : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value     : A
    satisfies : property value

record Group
  {ell : Level}
  (G : Set ell) :
  Set ell where

  field
    identity       : G
    inverse        : G -> G
    multiply       : G -> G -> G
    associative    : (x y z : G) ->
                     multiply (multiply x y) z ==
                     multiply x (multiply y z)
    identity-left  : (x : G) -> multiply identity x == x
    identity-right : (x : G) -> multiply x identity == x
    inverse-left   : (x : G) -> multiply (inverse x) x == identity
    inverse-right  : (x : G) -> multiply x (inverse x) == identity

open Group

power :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  Nat ->
  G
power structure x zero =
  identity structure
power structure x (suc exponent) =
  multiply structure (power structure x exponent) x

two : Nat
two =
  suc (suc zero)

three : Nat
three =
  suc two

putnam-1972-b3 :
  (ell : Level) ->
  Set (lsuc ell)
putnam-1972-b3 ell =
  (G : Set ell) ->
  (structure : Group G) ->
  (A B : G) ->
  multiply structure (multiply structure A B) A ==
    multiply structure
      (multiply structure B (power structure A two))
      B ->
  power structure A three == identity structure ->
  Exists Nat
    (\ k ->
      power structure B (suc (two * k)) == identity structure) ->
  B == identity structure
