-- Statement-only formalization of "Schroeder-Bernstein Theorem" from Hundred Theorems item 025.
-- This file contains no proof.

-- Hundred Theorems item 025, "Schroeder-Bernstein Theorem": under excluded middle,
-- injections between two sets in both directions imply a bijection. This is a
-- statement-only formalization and contains no proof.

open import Agda.Primitive using (Level; lsuc) renaming (_⊔_ to _lmax_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

data Empty : Set where

Not : {a : Level} -> Set a -> Set a
Not proposition = proposition -> Empty

IsProposition : {a : Level} -> Set a -> Set a
IsProposition proposition =
  (left right : proposition) -> left == right

IsSet : {a : Level} -> Set a -> Set a
IsSet A =
  (x y : A) -> IsProposition (x == y)

data Dec {a : Level} (proposition : Set a) : Set a where
  yes : proposition -> Dec proposition
  no  : Not proposition -> Dec proposition

ExcludedMiddleAt : (a : Level) -> Set (lsuc a)
ExcludedMiddleAt a =
  (proposition : Set a) ->
  IsProposition proposition ->
  Dec proposition

record Injection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a lmax b) where

  field
    map : A -> B
    map-injective :
      (x y : A) ->
      map x == map y ->
      x == y

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

schroeder-bernstein-theorem :
  {a b : Level} ->
  Set (lsuc (a lmax b))
schroeder-bernstein-theorem {a} {b} =
  ExcludedMiddleAt (a lmax b) ->
  (A : Set a) ->
  (B : Set b) ->
  IsSet A ->
  IsSet B ->
  Injection A B ->
  Injection B A ->
  Bijection A B
