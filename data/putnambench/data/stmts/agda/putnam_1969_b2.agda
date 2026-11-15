-- Statement-only formalization of PutnamBench corpus artifact putnam_1969_b2:
-- a finite group is not the union of two proper subgroups, while the analogous
-- assertion for three proper subgroups is false. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Level; lsuc; _⊔_)

infixr 3 _and_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a p : Level}
  (A : Set a)
  (property : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    satisfies : property value

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

record Finite
  {ℓ : Level}
  (A : Set ℓ) :
  Set ℓ where

  field
    cardinality : Nat
    finite-bijection : Bijection A (Fin cardinality)

record Group
  {ℓ : Level}
  (G : Set ℓ) :
  Set ℓ where

  field
    identity       : G
    inverse        : G -> G
    multiply       : G -> G -> G
    associative    : (x y z : G) ->
                     multiply x (multiply y z) ==
                     multiply (multiply x y) z
    identity-left  : (x : G) -> multiply identity x == x
    identity-right : (x : G) -> multiply x identity == x
    inverse-left   : (x : G) -> multiply (inverse x) x == identity
    inverse-right  : (x : G) -> multiply x (inverse x) == identity

record Subgroup
  {ℓ : Level}
  {G : Set ℓ}
  (structure : Group G) :
  Set (lsuc ℓ) where

  open Group structure

  field
    member : G -> Set ℓ
    membership-propositional :
      (x : G) ->
      (u v : member x) ->
      u == v
    contains-identity :
      member identity
    closed-under-inverse :
      (x : G) ->
      member x ->
      member (inverse x)
    closed-under-multiply :
      (x y : G) ->
      member x ->
      member y ->
      member (multiply x y)

open Subgroup

ProperSubgroup :
  {ℓ : Level} ->
  {G : Set ℓ} ->
  {structure : Group G} ->
  Subgroup structure ->
  Set ℓ
ProperSubgroup {G = G} subgroup =
  Not ((x : G) -> member subgroup x)

UnionCovers :
  {ℓ : Level} ->
  {G : Set ℓ} ->
  {structure : Group G} ->
  {n : Nat} ->
  (Fin n -> Subgroup structure) ->
  Set ℓ
UnionCovers {G = G} {n = n} subgroups =
  (x : G) ->
  Exists (Fin n) (\ i -> member (subgroups i) x)

NoCoverBy :
  (ℓ : Level) ->
  Nat ->
  Set (lsuc ℓ)
NoCoverBy ℓ n =
  (G : Set ℓ) ->
  (structure : Group G) ->
  Finite G ->
  (subgroups : Fin n -> Subgroup structure) ->
  ((i : Fin n) -> ProperSubgroup (subgroups i)) ->
  Not (UnionCovers subgroups)

two : Nat
two =
  suc (suc zero)

three : Nat
three =
  suc two

putnam-1969-b2-solution : Set
putnam-1969-b2-solution =
  Bottom

putnam-1969-b2 :
  (ℓ : Level) ->
  Set (lsuc (lsuc ℓ))
putnam-1969-b2 ℓ =
  (P : Nat -> Set (lsuc ℓ)) ->
  ((n : Nat) -> Iff (P n) (NoCoverBy ℓ n)) ->
  P two
  and
  Iff (P three) putnam-1969-b2-solution
