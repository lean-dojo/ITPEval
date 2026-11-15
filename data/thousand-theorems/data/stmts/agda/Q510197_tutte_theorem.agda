-- Statement-only formalization of thousand-theorems corpus artifact Q510197,
-- "Tutte theorem": a finite simple graph has a perfect matching exactly when
-- deleting any vertex subset leaves at most as many odd connected components
-- as deleted vertices. This file contains no proof.

{-# OPTIONS --safe #-}

module Q510197_tutte_theorem where

open import Agda.Primitive using (Level; lsuc) renaming (_⊔_ to _lmax_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _and_
infix 2 _iff_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not proposition =
  proposition -> Bottom

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a lmax b) where

  constructor both
  field
    first  : A
    second : B

record _iff_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a lmax b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a lmax p) where

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
  Set (a lmax b) where

  field
    to      : A -> B
    from    : B -> A
    from-to : (x : A) -> from (to x) == x
    to-from : (y : B) -> to (from y) == y

Finite :
  {a : Level} ->
  Set a ->
  Set a
Finite A =
  Exists Nat (\ cardinality -> Bijection A (Fin cardinality))

Subset :
  {a : Level} ->
  Set a ->
  Set (lsuc a)
Subset A =
  A -> Set _

record HasCardinality
  {a p : Level}
  {A : Set a}
  (member : A -> Set p)
  (cardinality : Nat) :
  Set (a lmax p) where

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

Odd :
  Nat ->
  Set
Odd n =
  Exists Nat (\ k -> n == suc (k + k))

OddCardinality :
  {a p : Level} ->
  {A : Set a} ->
  (A -> Set p) ->
  Set (a lmax p)
OddCardinality member =
  Exists Nat
    (\ cardinality ->
      HasCardinality member cardinality
      and
      Odd cardinality)

record SimpleGraph
  {a : Level}
  (V : Set a) :
  Set (lsuc a) where

  field
    adjacent :
      V ->
      V ->
      Set a
    loopless :
      (v : V) ->
      Not (adjacent v v)
    symmetric :
      (v w : V) ->
      adjacent v w ->
      adjacent w v

open SimpleGraph

data ConnectedOutside
  {a : Level}
  {V : Set a}
  (graph : SimpleGraph V)
  (removed : Subset V) :
  V ->
  V ->
  Set a where

  at :
    (v : V) ->
    Not (removed v) ->
    ConnectedOutside graph removed v v

  extend :
    {start current next : V} ->
    ConnectedOutside graph removed start current ->
    Not (removed next) ->
    adjacent graph current next ->
    ConnectedOutside graph removed start next

OddComponentAt :
  {a : Level} ->
  {V : Set a} ->
  SimpleGraph V ->
  Subset V ->
  V ->
  Set a
OddComponentAt graph removed representative =
  Not (removed representative)
  and
  OddCardinality
    (\ vertex ->
      ConnectedOutside graph removed representative vertex)

PairwiseDifferentComponents :
  {a : Level} ->
  {V : Set a} ->
  (graph : SimpleGraph V) ->
  (removed : Subset V) ->
  {count : Nat} ->
  (Fin count -> V) ->
  Set a
PairwiseDifferentComponents graph removed representatives =
  (left right : Fin _) ->
  Not (left == right) ->
  Not
    (ConnectedOutside graph removed
      (representatives left)
      (representatives right))

IsTutteViolator :
  {a : Level} ->
  {V : Set a} ->
  SimpleGraph V ->
  Subset V ->
  Set a
IsTutteViolator {V = V} graph removed =
  Exists Nat
    (\ removed-count ->
      HasCardinality removed removed-count
      and
      Exists (Fin (suc removed-count) -> V)
        (\ representatives ->
          ((index : Fin (suc removed-count)) ->
            OddComponentAt graph removed (representatives index))
          and
          PairwiseDifferentComponents graph removed representatives))

record IsPerfectMatching
  {a : Level}
  {V : Set a}
  (graph matching : SimpleGraph V) :
  Set a where

  field
    contained :
      (v w : V) ->
      adjacent matching v w ->
      adjacent graph v w
    unique-neighbor :
      (v left right : V) ->
      adjacent matching v left ->
      adjacent matching v right ->
      left == right
    covers :
      (v : V) ->
      Exists V (\ w -> adjacent matching v w)

tutte-theorem :
  {a : Level} ->
  Set (lsuc a)
tutte-theorem {a} =
  (V : Set a) ->
  Finite V ->
  (graph : SimpleGraph V) ->
  Exists (SimpleGraph V) (IsPerfectMatching graph)
  iff
  ((removed : Subset V) ->
    Not (IsTutteViolator graph removed))
