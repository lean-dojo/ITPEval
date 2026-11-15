-- Statement-only formalization of PutnamBench artifact
-- putnambench__agda__putnam_1968_a3: every finite type has an ordering of
-- all its subsets that starts with the empty subset and changes exactly one
-- element between consecutive subsets. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; lsuc) renaming (_⊔_ to _lmax_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom {a : Level} : Set a where

Not : {a : Level} -> Set a -> Set a
Not {a} proposition = proposition -> Bottom {a}

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

weaken :
  {n : Nat} ->
  Fin n ->
  Fin (suc n)
weaken fzero = fzero
weaken (fsuc i) = fsuc (weaken i)

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size : Nat
    to-fin : A -> Fin size
    from-fin : Fin size -> A
    from-to :
      (x : A) ->
      from-fin (to-fin x) == x
    to-from :
      (i : Fin size) ->
      to-fin (from-fin i) == i

Subset :
  {a : Level} ->
  Set a ->
  Set a
Subset A = A -> Bool

record SameSubset
  {a : Level}
  {A : Set a}
  (left right : Subset A) :
  Set a where

  field
    same-membership :
      (x : A) ->
      left x == right x

emptySubset :
  {a : Level}
  {A : Set a} ->
  Subset A
emptySubset _ = false

record ExistsUnique
  {a p : Level}
  (A : Set a)
  (property : A -> Set p) :
  Set (a lmax p) where

  field
    witness : A
    witness-property : property witness
    unique :
      (other : A) ->
      property other ->
      other == witness

record AddsOne
  {a : Level}
  {A : Set a}
  (before after : Subset A) :
  Set a where

  field
    element : A
    absent-before : before element == false
    present-after : after element == true
    unchanged-elsewhere :
      (x : A) ->
      Not (x == element) ->
      after x == before x

data OneElementChange
  {a : Level}
  {A : Set a}
  (left right : Subset A) :
  Set a where

  added :
    AddsOne left right ->
    OneElementChange left right
  removed :
    AddsOne right left ->
    OneElementChange left right

record GrayEnumeration
  {a : Level}
  (A : Set a) :
  Set a where

  field
    steps : Nat
    subsets : Fin (suc steps) -> Subset A
    starts-empty :
      SameSubset (subsets fzero) emptySubset
    every-subset-exactly-once :
      (target : Subset A) ->
      ExistsUnique
        (Fin (suc steps))
        (\ i -> SameSubset (subsets i) target)
    consecutive-change :
      (i : Fin steps) ->
      OneElementChange
        (subsets (weaken i))
        (subsets (fsuc i))

putnam-1968-a3 :
  {a : Level} ->
  Set (lsuc a)
putnam-1968-a3 {a} =
  (A : Set a) ->
  Finite A ->
  GrayEnumeration A
