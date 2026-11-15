-- Statement-only formalization of PutnamBench corpus artifact putnam_1997_a4:
-- a function on an arbitrary group whose triple products agree whenever both
-- input triples multiply to the identity can be left-translated into a group
-- homomorphism. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

infixr 3 _and_

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

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

putnam-1997-a4 :
  (ell : Level) ->
  Set (lsuc ell)
putnam-1997-a4 ell =
  (G : Set ell) ->
  (structure : Group G) ->
  (phi : G -> G) ->
  ((g1 g2 g3 h1 h2 h3 : G) ->
    (multiply structure (multiply structure g1 g2) g3 ==
       identity structure
     and
     multiply structure (multiply structure h1 h2) h3 ==
       identity structure) ->
    multiply structure
      (multiply structure (phi g1) (phi g2))
      (phi g3) ==
    multiply structure
      (multiply structure (phi h1) (phi h2))
      (phi h3)) ->
  Exists G
    (\ a ->
      (x y : G) ->
      multiply structure a
        (phi (multiply structure x y)) ==
      multiply structure
        (multiply structure a (phi x))
        (multiply structure a (phi y)))
