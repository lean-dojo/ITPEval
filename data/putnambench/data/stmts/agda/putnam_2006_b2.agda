-- Statement-only formalization of PutnamBench corpus artifact putnam_2006_b2
-- (putnambench__agda__putnam_2006_b2): every nonempty finite set of n real
-- numbers has a nonempty subset whose sum differs from an integer by at most
-- 1 / (n + 1). This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2006B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<_ _!=_
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

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc  : {m n : Nat} -> m < n -> suc m < suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective function =
  (x y : _) ->
  function x == function y ->
  x == y

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

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

maximum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left _ =
  y
... | right _ =
  x

absoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
absoluteValue reals x =
  maximum reals x (negate reals x)

integerToReal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
integerToReal reals (pos n) =
  fromNat reals n
integerToReal reals (negsuc n) =
  negate reals (fromNat reals (suc n))

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (n : Nat) ->
  (Fin n -> R) ->
  R
sumFin reals zero terms =
  zeroR reals
sumFin reals (suc n) terms =
  add reals
    (terms fzero)
    (sumFin reals n (\ i -> terms (fsuc i)))

module Putnam2006B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  SubsetBound :
    {n : Nat} ->
    (Fin n -> R) ->
    Set
  SubsetBound {n} elements =
    Exists Nat
      (\ k ->
        zero < k
        and
        Exists (Fin k -> Fin n)
          (\ select ->
            Injective select
            and
            Exists Int
              (\ integer ->
                lessOrEqual reals
                  (absoluteValue reals
                    (add reals
                      (integerToReal reals integer)
                      (sumFin reals k
                        (\ i -> elements (select i)))))
                  (divide reals
                    (oneR reals)
                    (fromNat reals (suc n))))))

  proposition : Set
  proposition =
    (n : Nat) ->
    zero < n ->
    (elements : Fin n -> R) ->
    Injective elements ->
    SubsetBound elements

putnam-2006-b2 : Set1
putnam-2006-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2006B2Statement.proposition reals
