-- Statement-only formalization of PutnamBench corpus artifact putnam_1965_b5:
-- if 4E is at most V squared, a finite V-vertex simple graph with exactly E
-- edges and no triangle exists. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

infix 4 _<=N_
infixr 3 _and_

data Bottom : Set where

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
  (P : A -> Set p) :
  Set (a ⊔ p) where

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

record OrderedPair
  {a : Level}
  (A : Set a) :
  Set a where

  constructor _,_
  field
    left  : A
    right : A

open OrderedPair

FiniteCarrier :
  {a : Level} ->
  Set a ->
  Nat ->
  Set a
FiniteCarrier A cardinality =
  Bijection A (Fin cardinality)

Simple :
  {a : Level} ->
  {A : Set a} ->
  (A -> A -> Bool) ->
  Set a
Simple {A = A} adjacent =
  ((v : A) -> adjacent v v == false)
  and
  ((v w : A) -> adjacent v w == adjacent w v)

record DirectedEdgesHaveCardinality
  {a : Level}
  {A : Set a}
  (adjacent : A -> A -> Bool)
  (cardinality : Nat) :
  Set a where

  field
    enumerate :
      Fin cardinality ->
      OrderedPair A

    enumerated-edge :
      (i : Fin cardinality) ->
      adjacent (left (enumerate i)) (right (enumerate i)) == true

    enumeration-complete :
      (u v : A) ->
      adjacent u v == true ->
      Exists (Fin cardinality)
        (\ i -> enumerate i == (u , v))

    enumeration-injective :
      (i j : Fin cardinality) ->
      enumerate i == enumerate j ->
      i == j

TriangleFree :
  {a : Level} ->
  {A : Set a} ->
  (A -> A -> Bool) ->
  Set a
TriangleFree {A = A} adjacent =
  (a b c : A) ->
  adjacent a b == true ->
  adjacent a c == true ->
  adjacent b c == true ->
  Bottom

two : Nat
two =
  suc (suc zero)

four : Nat
four =
  suc (suc (suc (suc zero)))

putnam-1965-b5 :
  {a : Level} ->
  Set (lsuc a)
putnam-1965-b5 {a} =
  (A : Set a) ->
  (V E : Nat) ->
  FiniteCarrier A V ->
  four * E <=N V * V ->
  Exists (A -> A -> Bool)
    (\ adjacent ->
      Simple adjacent
      and
      (DirectedEdgesHaveCardinality adjacent (two * E)
      and
      TriangleFree adjacent))
