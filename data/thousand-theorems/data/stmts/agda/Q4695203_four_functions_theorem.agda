-- Statement-only formalization of thousand-theorems corpus artifact Q4695203
-- (thousand-theorems__agda__Q4695203), "Four functions theorem": the
-- Ahlswede-Daykin inequality for nonnegative functions on an arbitrary
-- distributive lattice and two finite subsets. This file contains no proof.

{-# OPTIONS --safe #-}

module Q4695203_four_functions_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} proposition =
  proposition -> Bottom {a}

record Both
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> Either A B
  right : B -> Either A B

record Exists
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

  constructor witness
  field
    value    : A
    property : P value

record DecidableEquality
  {a : Level}
  (A : Set a) :
  Set a where

  field
    equal : A -> A -> Bool
    equal-sound :
      (x y : A) ->
      equal x y == true ->
      x == y
    equal-complete :
      (x y : A) ->
      x == y ->
      equal x y == true

open DecidableEquality

contains :
  {a : Level}
  {A : Set a} ->
  DecidableEquality A ->
  A ->
  List A ->
  Bool
contains equality x [] =
  false
contains equality x (y ∷ ys) with equal equality x y
... | true =
  true
... | false =
  contains equality x ys

data NoDuplicates
  {a : Level}
  {A : Set a}
  (equality : DecidableEquality A) :
  List A ->
  Set a where

  no-duplicates-empty :
    NoDuplicates equality []
  no-duplicates-cons :
    {x : A} ->
    {xs : List A} ->
    contains equality x xs == false ->
    NoDuplicates equality xs ->
    NoDuplicates equality (x ∷ xs)

record FiniteSet
  {a : Level}
  (A : Set a)
  (equality : DecidableEquality A) :
  Set a where

  constructor finite-set
  field
    elements      : List A
    no-duplicates : NoDuplicates equality elements

open FiniteSet

insertUnique :
  {a : Level}
  {A : Set a} ->
  DecidableEquality A ->
  A ->
  List A ->
  List A
insertUnique equality x xs with contains equality x xs
... | true =
  xs
... | false =
  x ∷ xs

deduplicate :
  {a : Level}
  {A : Set a} ->
  DecidableEquality A ->
  List A ->
  List A
deduplicate equality [] =
  []
deduplicate equality (x ∷ xs) =
  insertUnique equality x (deduplicate equality xs)

mapList :
  {a b : Level}
  {A : Set a}
  {B : Set b} ->
  (A -> B) ->
  List A ->
  List B
mapList f [] =
  []
mapList f (x ∷ xs) =
  f x ∷ mapList f xs

append :
  {a : Level}
  {A : Set a} ->
  List A ->
  List A ->
  List A
append [] ys =
  ys
append (x ∷ xs) ys =
  x ∷ append xs ys

concatMap :
  {a b : Level}
  {A : Set a}
  {B : Set b} ->
  (A -> List B) ->
  List A ->
  List B
concatMap f [] =
  []
concatMap f (x ∷ xs) =
  append (f x) (concatMap f xs)

pairwiseValues :
  {a : Level}
  {A : Set a} ->
  (A -> A -> A) ->
  List A ->
  List A ->
  List A
pairwiseValues operation xs ys =
  concatMap
    (\ x -> mapList (\ y -> operation x y) ys)
    xs

pairwiseImageElements :
  {a : Level}
  {A : Set a} ->
  DecidableEquality A ->
  (A -> A -> A) ->
  List A ->
  List A ->
  List A
pairwiseImageElements equality operation xs ys =
  deduplicate equality (pairwiseValues operation xs ys)

record DistributiveLattice
  {a : Level}
  (A : Set a) :
  Set a where

  field
    meet join : A -> A -> A

    meet-associative :
      (x y z : A) ->
      meet (meet x y) z == meet x (meet y z)
    meet-commutative :
      (x y : A) ->
      meet x y == meet y x
    meet-idempotent :
      (x : A) ->
      meet x x == x

    join-associative :
      (x y z : A) ->
      join (join x y) z == join x (join y z)
    join-commutative :
      (x y : A) ->
      join x y == join y x
    join-idempotent :
      (x : A) ->
      join x x == x

    meet-absorption :
      (x y : A) ->
      meet x (join x y) == x
    join-absorption :
      (x y : A) ->
      join x (meet x y) == x

    meet-distributes-over-join :
      (x y z : A) ->
      meet x (join y z) ==
      join (meet x y) (meet x z)
    join-distributes-over-meet :
      (x y z : A) ->
      join x (meet y z) ==
      meet (join x y) (join x z)

open DistributiveLattice

record StrictOrderedCommutativeSemiring
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zero one : R
    add multiply : R -> R -> R
    lessOrEqual : R -> R -> Set r

    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-commutative :
      (x y : R) ->
      add x y == add y x
    add-zero-left :
      (x : R) ->
      add zero x == x
    add-zero-right :
      (x : R) ->
      add x zero == x

    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-commutative :
      (x y : R) ->
      multiply x y == multiply y x
    multiply-one-left :
      (x : R) ->
      multiply one x == x
    multiply-one-right :
      (x : R) ->
      multiply x one == x

    distribute-left :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    distribute-right :
      (x y z : R) ->
      multiply (add x y) z ==
      add (multiply x z) (multiply y z)
    multiply-zero-left :
      (x : R) ->
      multiply zero x == zero
    multiply-zero-right :
      (x : R) ->
      multiply x zero == zero

    order-reflexive :
      (x : R) ->
      lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      Either (lessOrEqual x y) (lessOrEqual y x)

    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    add-order-cancellation :
      (x y z : R) ->
      lessOrEqual (add x y) (add x z) ->
      lessOrEqual y z

    zero-less-or-equal-one :
      lessOrEqual zero one
    different-elements :
      Exists R (\ x -> Exists R (\ y -> Not (x == y)))

    multiply-strict-left :
      (x y z : R) ->
      Both (lessOrEqual zero x) (Not (zero == x)) ->
      Both (lessOrEqual y z) (Not (y == z)) ->
      Both
        (lessOrEqual (multiply x y) (multiply x z))
        (Not (multiply x y == multiply x z))
    multiply-strict-right :
      (x y z : R) ->
      Both (lessOrEqual zero z) (Not (zero == z)) ->
      Both (lessOrEqual x y) (Not (x == y)) ->
      Both
        (lessOrEqual (multiply x z) (multiply y z))
        (Not (multiply x z == multiply y z))

    exists-add-of-less-or-equal :
      (x y : R) ->
      lessOrEqual x y ->
      Exists R (\ z -> y == add x z)

open StrictOrderedCommutativeSemiring

sumList :
  {a r : Level}
  {A : Set a}
  {R : Set r} ->
  StrictOrderedCommutativeSemiring R ->
  (A -> R) ->
  List A ->
  R
sumList coefficients f [] =
  zero coefficients
sumList coefficients f (x ∷ xs) =
  add coefficients (f x) (sumList coefficients f xs)

sumFiniteSet :
  {a r : Level}
  {A : Set a}
  {R : Set r} ->
  (coefficients : StrictOrderedCommutativeSemiring R) ->
  {equality : DecidableEquality A} ->
  (A -> R) ->
  FiniteSet A equality ->
  R
sumFiniteSet coefficients f set =
  sumList coefficients f (elements set)

sumPairwiseImage :
  {a r : Level}
  {A : Set a}
  {R : Set r} ->
  (coefficients : StrictOrderedCommutativeSemiring R) ->
  (equality : DecidableEquality A) ->
  (A -> A -> A) ->
  (A -> R) ->
  FiniteSet A equality ->
  FiniteSet A equality ->
  R
sumPairwiseImage coefficients equality operation f s t =
  sumList coefficients f
    (pairwiseImageElements equality operation
      (elements s)
      (elements t))

four-functions-theorem : Setω
four-functions-theorem =
  {a r : Level} ->
  (A : Set a) ->
  (lattice : DistributiveLattice A) ->
  (equality : DecidableEquality A) ->
  (R : Set r) ->
  (coefficients : StrictOrderedCommutativeSemiring R) ->
  (f1 f2 f3 f4 : A -> R) ->
  ((x : A) ->
    lessOrEqual coefficients (zero coefficients) (f1 x)) ->
  ((x : A) ->
    lessOrEqual coefficients (zero coefficients) (f2 x)) ->
  ((x : A) ->
    lessOrEqual coefficients (zero coefficients) (f3 x)) ->
  ((x : A) ->
    lessOrEqual coefficients (zero coefficients) (f4 x)) ->
  ((x y : A) ->
    lessOrEqual coefficients
      (multiply coefficients (f1 x) (f2 y))
      (multiply coefficients
        (f3 (meet lattice x y))
        (f4 (join lattice x y)))) ->
  (s t : FiniteSet A equality) ->
  lessOrEqual coefficients
    (multiply coefficients
      (sumFiniteSet coefficients f1 s)
      (sumFiniteSet coefficients f2 t))
    (multiply coefficients
      (sumPairwiseImage coefficients equality
        (meet lattice) f3 s t)
      (sumPairwiseImage coefficients equality
        (join lattice) f4 s t))
