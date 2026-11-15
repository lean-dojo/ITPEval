-- Statement-only formalization of "Dissection of Cubes (into Cubes)" from Hundred Theorems item
-- 082. This file contains no proof.

module HundredTheorems082 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_
infix 2 _iff_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
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
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum) and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  CompleteOrderedField.lessOrEqual reals x y and x != y

Point : Set -> Set
Point R = Fin (suc (suc (suc zero))) -> R

Region : Set -> Set1
Region R = Point R -> Set

record Cube
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set where

  constructor cube
  field
    lower : Point R
    width : R
    positive-width :
      StrictLess reals
        (CompleteOrderedField.zeroR reals)
        width

open Cube public

cube-region :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  Cube reals ->
  Region R
cube-region {R} reals c p =
  (axis : Fin (suc (suc (suc zero)))) ->
  CompleteOrderedField.lessOrEqual reals
    (lower c axis)
    (p axis) and
  StrictLess reals
    (p axis)
    (CompleteOrderedField.add reals
      (lower c axis)
      (width c))

Disjoint :
  {R : Set} ->
  Region R ->
  Region R ->
  Set
Disjoint {R} left-region right-region =
  (p : Point R) ->
  left-region p ->
  right-region p ->
  Bottom

RegionEqual :
  {R : Set} ->
  Region R ->
  Region R ->
  Set
RegionEqual {R} left-region right-region =
  (p : Point R) ->
  left-region p iff right-region p

FiniteUnion :
  {R : Set} ->
  {count : Nat} ->
  (reals : CompleteOrderedField R) ->
  (Fin count -> Cube reals) ->
  Region R
FiniteUnion {count = count} reals pieces p =
  Exists (Fin count)
    (\ i -> cube-region reals (pieces i) p)

PairwiseDisjoint :
  {R : Set} ->
  {count : Nat} ->
  (reals : CompleteOrderedField R) ->
  (Fin count -> Cube reals) ->
  Set
PairwiseDisjoint {count = count} reals pieces =
  (i j : Fin count) ->
  i != j ->
  Disjoint
    (cube-region reals (pieces i))
    (cube-region reals (pieces j))

WidthsInjective :
  {R : Set} ->
  {count : Nat} ->
  {reals : CompleteOrderedField R} ->
  (Fin count -> Cube reals) ->
  Set
WidthsInjective {count = count} pieces =
  (i j : Fin count) ->
  width (pieces i) == width (pieces j) ->
  i == j

TwoOrMore : Nat -> Set
TwoOrMore count =
  suc (suc zero) <=N count

dissection-of-cubes-into-cubes : Set1
dissection-of-cubes-into-cubes =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (target : Cube reals) ->
  (count : Nat) ->
  TwoOrMore count ->
  (pieces : Fin count -> Cube reals) ->
  PairwiseDisjoint reals pieces ->
  RegionEqual
    (FiniteUnion reals pieces)
    (cube-region reals target) ->
  WidthsInjective pieces ->
  Bottom
