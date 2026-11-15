-- Statement-only formalization of PutnamBench corpus artifact putnam_1996_a4:
-- a consistent orientation of the distinct triples of a finite set admits an
-- injective real-valued ordering whose increasing triples have that orientation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1996A4 where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

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
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    cardinality : Nat
    to-fin       : A -> Fin cardinality
    from-fin     : Fin cardinality -> A
    from-to      : (x : A) -> from-fin (to-fin x) == x
    to-from      : (i : Fin cardinality) -> to-fin (from-fin i) == i

record CompleteOrderedRealField (R : Set) : Set1 where
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
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
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
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

StrictlyLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictlyLess reals x y =
  lessOrEqual reals x y
  and
  x != y

Injective :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (A -> B) ->
  Set (a ⊔ b)
Injective {A = A} f =
  (x y : A) ->
  f x == f y ->
  x == y

PairwiseDistinct3 :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  A ->
  Set a
PairwiseDistinct3 a b c =
  a != b
  and
  b != c
  and
  a != c

PairwiseDistinct4 :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  A ->
  A ->
  Set a
PairwiseDistinct4 a b c d =
  a != b
  and
  a != c
  and
  a != d
  and
  b != c
  and
  b != d
  and
  c != d

putnam-1996-a4 :
  {a : Level} ->
  Set (lsuc a)
putnam-1996-a4 {a} =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (A : Set a) ->
  Finite A ->
  (S : A -> A -> A -> Set a) ->
  ((x y z : A) ->
    S x y z ->
    PairwiseDistinct3 x y z) ->
  ((a b c : A) ->
    PairwiseDistinct3 a b c ->
    Iff
      (S a b c)
      (S b c a)) ->
  ((a b c : A) ->
    PairwiseDistinct3 a b c ->
    Iff
      (S a b c)
      (Not (S c b a))) ->
  ((a b c d : A) ->
    PairwiseDistinct4 a b c d ->
    Iff
      (S a b c and S c d a)
      (S b c d and S d a b)) ->
  Exists (A -> R)
    (\ g ->
      Injective g
      and
      ((a b c : A) ->
        StrictlyLess reals (g a) (g b)
        and
        StrictlyLess reals (g b) (g c) ->
        S a b c))
