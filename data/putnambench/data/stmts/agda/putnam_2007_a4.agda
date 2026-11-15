-- Statement-only formalization of PutnamBench corpus artifact putnam_2007_a4
-- (putnambench__agda__putnam_2007_a4): classification of real polynomials
-- that map every base-10 repunit to a repunit. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<=Z_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data _<=Z_ : Int -> Int -> Set where
  pos<=posZ :
    {m n : Nat} ->
    m <=N n ->
    pos m <=Z pos n
  neg<=posZ :
    {m n : Nat} ->
    negsuc m <=Z pos n
  neg<=negZ :
    {m n : Nat} ->
    n <=N m ->
    negsuc m <=Z negsuc n

oneN : Nat
oneN =
  suc zero

nineN : Nat
nineN =
  suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

tenN : Nat
tenN =
  suc nineN

oneMinusNat : Nat -> Int
oneMinusNat zero =
  pos oneN
oneMinusNat (suc zero) =
  pos zero
oneMinusNat (suc (suc n)) =
  negsuc n

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

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals (naturalPower reals x n) x

integerPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Int ->
  R
integerPower reals x (pos n) =
  naturalPower reals x n
integerPower reals x (negsuc n) =
  inverse reals (naturalPower reals x (suc n))

Polynomial : Set -> Set
Polynomial R =
  List R

evaluate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  R
evaluate reals [] x =
  zeroR reals
evaluate reals (coefficient ∷ coefficients) x =
  add reals coefficient
    (multiply reals x (evaluate reals coefficients x))

repunitValue : Nat -> Nat
repunitValue zero =
  oneN
repunitValue (suc n) =
  tenN * repunitValue n + oneN

module Putnam2007A4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Repunit : R -> Set
  Repunit x =
    Exists Nat
      (\ digitsMinusOne ->
        x ==
        fromNat reals
          (repunitValue digitsMinusOne))

  PreservesRepunits :
    Polynomial R ->
    Set
  PreservesRepunits polynomial =
    (x : R) ->
    Repunit x ->
    Repunit (evaluate reals polynomial x)

  solutionValue :
    Nat ->
    Int ->
    R ->
    R
  solutionValue d c x =
    divide reals
      (subtract reals
        (multiply reals
          (integerPower reals (fromNat reals tenN) c)
          (naturalPower reals
            (add reals
              (multiply reals
                (fromNat reals nineN)
                x)
              (oneR reals))
            d))
        (oneR reals))
      (fromNat reals nineN)

  IsSolution :
    Polynomial R ->
    Set
  IsSolution polynomial =
    Exists Nat
      (\ d ->
        Exists Int
          (\ c ->
            oneMinusNat d <=Z c
            and
            ((x : R) ->
              evaluate reals polynomial x ==
              solutionValue d c x)))

  proposition : Set
  proposition =
    (polynomial : Polynomial R) ->
    PreservesRepunits polynomial
    iff
    IsSolution polynomial

putnam-2007-a4 : Set1
putnam-2007-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2007A4Statement.proposition reals
