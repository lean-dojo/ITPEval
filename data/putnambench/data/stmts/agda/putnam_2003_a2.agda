-- Statement-only formalization of PutnamBench corpus artifact putnam_2003_a2
-- (putnambench__agda__putnam_2003_a2): Minkowski's inequality for the nth
-- roots of products of two finite families of nonnegative real numbers.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2003A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat -> Set where
  positive :
    {n : Nat} ->
    Positive (suc n)

data Fin : Nat -> Set where
  fzero :
    {n : Nat} ->
    Fin (suc n)
  fsuc :
    {n : Nat} ->
    Fin n ->
    Fin (suc n)

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
      (x y : R) ->
      add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) ->
      add x zeroR == x
    add-inverse :
      (x : R) ->
      add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) ->
      multiply x oneR == x
    multiply-zero :
      (x : R) ->
      multiply x zeroR == zeroR
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
      Exists Nat
        (\ n ->
          lessOrEqual x (fromNat n))
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

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

productFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
productFin reals {zero} term =
  oneR reals
productFin reals {suc n} term =
  multiply reals
    (term fzero)
    (productFin reals (\ i -> term (fsuc i)))

record StandardPositiveNthRoots
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    nthRoot :
      (n : Nat) ->
      Positive n ->
      R ->
      R

    nth-root-nonnegative :
      (n : Nat) ->
      (hn : Positive n) ->
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      lessOrEqual reals
        (zeroR reals)
        (nthRoot n hn x)

    nth-root-power :
      (n : Nat) ->
      (hn : Positive n) ->
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      naturalPower reals (nthRoot n hn x) n == x

    nth-root-unique :
      (n : Nat) ->
      (hn : Positive n) ->
      (x y : R) ->
      lessOrEqual reals (zeroR reals) x ->
      lessOrEqual reals (zeroR reals) y ->
      naturalPower reals y n == x ->
      y == nthRoot n hn x

open StandardPositiveNthRoots

module Putnam2003A2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (roots : StandardPositiveNthRoots reals) where

  proposition : Set
  proposition =
    (n : Nat) ->
    (hn : Positive n) ->
    (a b : Fin n -> R) ->
    ((i : Fin n) ->
      lessOrEqual reals (zeroR reals) (a i)
      and
      lessOrEqual reals (zeroR reals) (b i)) ->
    lessOrEqual reals
      (add reals
        (nthRoot roots n hn (productFin reals a))
        (nthRoot roots n hn (productFin reals b)))
      (nthRoot roots n hn
        (productFin reals
          (\ i -> add reals (a i) (b i))))

putnam-2003-a2 : Set1
putnam-2003-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (roots : StandardPositiveNthRoots reals) ->
  Putnam2003A2Statement.proposition reals roots
