-- Statement-only formalization of thousand-theorems corpus artifact Q17005116
-- (thousand-theorems__agda__Q17005116), "Birkhoff's representation theorem":
-- the canonical map from a finite
-- distributive lattice to the powerset of its sup-irreducible elements is an
-- injective lattice homomorphism. This file contains no proof.

{-# OPTIONS --safe #-}

module Q17005116_birkhoff_s_representation_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _and_
infixr 2 _or_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} proposition =
  proposition -> Bottom {a}

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

data Decision
  {a : Level}
  (A : Set a) :
  Set a where

  yes : A -> Decision A
  no  : Not A -> Decision A

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size : Nat
    encode : A -> Fin size
    decode : Fin size -> A
    encode-decode :
      (index : Fin size) ->
      encode (decode index) == index
    decode-encode :
      (x : A) ->
      decode (encode x) == x

record DistributiveLattice
  {a : Level}
  (A : Set a) :
  Set a where

  field
    join : A -> A -> A
    meet : A -> A -> A

    join-associative :
      (x y z : A) ->
      join (join x y) z == join x (join y z)
    join-commutative :
      (x y : A) ->
      join x y == join y x
    join-idempotent :
      (x : A) ->
      join x x == x

    meet-associative :
      (x y z : A) ->
      meet (meet x y) z == meet x (meet y z)
    meet-commutative :
      (x y : A) ->
      meet x y == meet y x
    meet-idempotent :
      (x : A) ->
      meet x x == x

    join-absorption :
      (x y : A) ->
      join x (meet x y) == x
    meet-absorption :
      (x y : A) ->
      meet x (join x y) == x

    join-distributes-over-meet :
      (x y z : A) ->
      join x (meet y z) ==
      meet (join x y) (join x z)
    meet-distributes-over-join :
      (x y z : A) ->
      meet x (join y z) ==
      join (meet x y) (meet x z)

open DistributiveLattice

LessOrEqual :
  {a : Level} ->
  {A : Set a} ->
  DistributiveLattice A ->
  A ->
  A ->
  Set a
LessOrEqual lattice x y =
  join lattice x y == y

record SupIrreducible
  {a : Level}
  {A : Set a}
  (lattice : DistributiveLattice A)
  (x : A) :
  Set a where

  field
    not-least :
      Not ((y : A) -> LessOrEqual lattice x y)
    irreducible :
      (y z : A) ->
      join lattice y z == x ->
      (y == x) or (z == x)

record SupIrreducibleElement
  {a : Level}
  {A : Set a}
  (lattice : DistributiveLattice A) :
  Set a where

  field
    value : A
    is-sup-irreducible : SupIrreducible lattice value

open SupIrreducibleElement

Predicate :
  {a : Level} ->
  Set a ->
  Set (lsuc a)
Predicate {a} A =
  A -> Set a

SetEqual :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Set a
SetEqual {A = A} P Q =
  (x : A) -> Iff (P x) (Q x)

Union :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Predicate A
Union P Q x =
  P x or Q x

Intersection :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Predicate A
Intersection P Q x =
  P x and Q x

BirkhoffSet :
  {a : Level} ->
  {A : Set a} ->
  (lattice : DistributiveLattice A) ->
  A ->
  Predicate (SupIrreducibleElement lattice)
BirkhoffSet lattice x irreducible-element =
  LessOrEqual lattice (value irreducible-element) x

record IsInjectiveLatticeHomomorphism
  {a : Level}
  {A : Set a}
  (lattice : DistributiveLattice A)
  (map :
    A ->
    Predicate (SupIrreducibleElement lattice)) :
  Set a where

  field
    map-join :
      (x y : A) ->
      SetEqual
        (map (join lattice x y))
        (Union (map x) (map y))
    map-meet :
      (x y : A) ->
      SetEqual
        (map (meet lattice x y))
        (Intersection (map x) (map y))
    injective :
      (x y : A) ->
      SetEqual (map x) (map y) ->
      x == y

birkhoff-s-representation-theorem :
  {a : Level} ->
  Set (lsuc a)
birkhoff-s-representation-theorem {a} =
  (A : Set a) ->
  (lattice : DistributiveLattice A) ->
  Finite A ->
  ((x : A) -> Decision (SupIrreducible lattice x)) ->
  IsInjectiveLatticeHomomorphism lattice (BirkhoffSet lattice)
