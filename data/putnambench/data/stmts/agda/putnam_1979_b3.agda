-- Statement-only formalization of PutnamBench corpus artifact putnam_1979_b3:
-- over a finite field of odd cardinality n, exactly (n - 1) / 2 constant
-- shifts of a monic irreducible quadratic remain irreducible. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

infix 4 _!=_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not proposition =
  proposition -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to      : A -> B
    from    : B -> A
    from-to : (x : A) -> from (to x) == x
    to-from : (y : B) -> to (from y) == y

record HasCardinality
  {a : Level}
  {A : Set a}
  (member : A -> Set a)
  (cardinality : Nat) :
  Set a where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record Field
  {a : Level}
  (F : Set a) :
  Set (lsuc a) where

  field
    zeroF oneF : F
    add multiply : F -> F -> F
    negate inverse : F -> F

    one-not-zero :
      oneF != zeroF

    add-commutative :
      (x y : F) -> add x y == add y x
    add-associative :
      (x y z : F) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : F) -> add x zeroF == x
    add-inverse :
      (x : F) -> add x (negate x) == zeroF

    multiply-commutative :
      (x y : F) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : F) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : F) -> multiply x oneF == x
    multiply-zero :
      (x : F) -> multiply x zeroF == zeroF
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

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

half : Nat -> Nat
half zero =
  zero
half (suc zero) =
  zero
half (suc (suc n)) =
  suc (half n)

putnam-1979-b3-solution : Nat -> Nat
putnam-1979-b3-solution n =
  half (n - one)

Odd : Nat -> Set
Odd n =
  Exists Nat
    (\ k -> n == suc (two * k))

quadraticValue :
  {a : Level} ->
  {F : Set a} ->
  Field F ->
  F ->
  F ->
  F ->
  F
quadraticValue algebra b c x =
  add algebra
    (add algebra
      (multiply algebra x x)
      (multiply algebra b x))
    c

IrreducibleMonicQuadratic :
  {a : Level} ->
  {F : Set a} ->
  Field F ->
  F ->
  F ->
  Set a
IrreducibleMonicQuadratic {F = F} algebra b c =
  (x : F) ->
  quadraticValue algebra b c x != zeroF algebra

module Putnam1979B3Statement
  {a : Level}
  {F : Set a}
  (algebra : Field F) where

  proposition : Set a
  proposition =
    (n : Nat) ->
    Bijection F (Fin n) ->
    Odd n ->
    (b c : F) ->
    IrreducibleMonicQuadratic algebra b c ->
    HasCardinality
      (\ d ->
        IrreducibleMonicQuadratic algebra b (add algebra c d))
      (putnam-1979-b3-solution n)

putnam-1979-b3 :
  {a : Level} ->
  Set (lsuc a)
putnam-1979-b3 {a} =
  (F : Set a) ->
  (algebra : Field F) ->
  Putnam1979B3Statement.proposition algebra
