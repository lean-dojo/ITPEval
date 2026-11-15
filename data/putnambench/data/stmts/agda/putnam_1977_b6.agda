-- Statement-only formalization of PutnamBench corpus artifact putnam_1977_b6:
-- a finite subgroup H of order h satisfying (x a)^3 = 1 has at most 3 h^2
-- distinct nonempty alternating products x1 a ... xn a. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1977B6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

infix 4 _<=N_
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
    value     : A
    satisfies : property value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {a p : Level}
  {A : Set a}
  (P : A -> Set p)
  (cardinality : Nat) :
  Set (a ⊔ p) where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin cardinality)
        (\ index -> x == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

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

record Subgroup
  {ell p : Level}
  {G : Set ell}
  (structure : Group G)
  (member : G -> Set p) :
  Set (ell ⊔ p) where

  open Group structure

  field
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

data All
  {a p : Level}
  {A : Set a}
  (P : A -> Set p) :
  List A ->
  Set (a ⊔ p) where

  all[]  : All P []
  _all∷_ : {x : A} {xs : List A} ->
           P x ->
           All P xs ->
           All P (x ∷ xs)

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
  multiply structure x (power structure x exponent)

alternatingProduct :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  List G ->
  G
alternatingProduct structure a [] =
  identity structure
alternatingProduct structure a (x ∷ xs) =
  multiply structure
    (multiply structure x a)
    (alternatingProduct structure a xs)

ProductWord :
  {ell p : Level} ->
  {G : Set ell} ->
  (structure : Group G) ->
  (member : G -> Set p) ->
  G ->
  G ->
  Set (ell ⊔ p)
ProductWord {G = G} structure member a g =
  Exists G
    (\ x ->
      member x
      and
      Exists (List G)
        (\ xs ->
          All member xs
          and
          g ==
          multiply structure
            (multiply structure x a)
            (alternatingProduct structure a xs)))

three : Nat
three =
  suc (suc (suc zero))

putnam-1977-b6 :
  (ell p q : Level) ->
  Set (lsuc (ell ⊔ (p ⊔ q)))
putnam-1977-b6 ell p q =
  (G : Set ell) ->
  (structure : Group G) ->
  (H : G -> Set p) ->
  Subgroup structure H ->
  (h : Nat) ->
  HasCardinality H h ->
  (a : G) ->
  ((x : G) ->
    H x ->
    power structure (multiply structure x a) three ==
    identity structure) ->
  (P : G -> Set q) ->
  ((g : G) ->
    Iff (P g) (ProductWord structure H a g)) ->
  Exists Nat
    (\ cardinality ->
      HasCardinality P cardinality
      and
      cardinality <=N three * (h * h))
