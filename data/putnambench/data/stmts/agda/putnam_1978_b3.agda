-- Statement-only formalization of PutnamBench corpus artifact putnam_1978_b3:
-- the greatest real roots of a recursively defined polynomial sequence are
-- strictly increasing and converge to zero. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

Positive : Nat -> Set
Positive n =
  oneN <=N n

NatStrictLess : Nat -> Nat -> Set
NatStrictLess m n =
  suc m <=N n

natPredecessor : Nat -> Nat
natPredecessor zero =
  zero
natPredecessor (suc n) =
  n

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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals (subtract reals center radius) x
  and
  StrictLess reals x (add reals center radius)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

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

addPolynomials :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
addPolynomials reals [] ys =
  ys
addPolynomials reals xs [] =
  xs
addPolynomials reals (x ∷ xs) (y ∷ ys) =
  add reals x y ∷
  addPolynomials reals xs ys

scaleCoefficients :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Polynomial R ->
  Polynomial R
scaleCoefficients reals scalar [] =
  []
scaleCoefficients reals scalar (coefficient ∷ coefficients) =
  multiply reals scalar coefficient ∷
  scaleCoefficients reals scalar coefficients

scaleByX :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Polynomial R ->
  Polynomial R
scaleByX reals scalar [] =
  []
scaleByX reals scalar coefficients =
  zeroR reals ∷ scaleCoefficients reals scalar coefficients

PolynomialEqual :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R ->
  Set
PolynomialEqual {R} reals xs ys =
  (x : R) ->
  evaluate reals xs x == evaluate reals ys x

IsRoot :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  Set
IsRoot reals polynomial x =
  evaluate reals polynomial x == zeroR reals

module Putnam1978B3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  PolynomialRecurrence :
    (Nat -> Polynomial R) ->
    Set
  PolynomialRecurrence P =
    PolynomialEqual reals
      (P oneN)
      (oneR reals ∷ oneR reals ∷ [])
    and
    PolynomialEqual reals
      (P twoN)
      (oneR reals ∷ fromNat reals twoN ∷ [])
    and
    ((n : Nat) ->
      Positive n ->
      PolynomialEqual reals
        (P (twoN * n + oneN))
        (addPolynomials reals
          (P (twoN * n))
          (scaleByX reals
            (fromNat reals (suc n))
            (P (natPredecessor (twoN * n))))))
    and
    ((n : Nat) ->
      Positive n ->
      PolynomialEqual reals
        (P (twoN * n + twoN))
        (addPolynomials reals
          (P (twoN * n + oneN))
          (scaleByX reals
            (fromNat reals (suc n))
            (P (twoN * n)))))

  GreatestRootSequence :
    (Nat -> Polynomial R) ->
    (Nat -> R) ->
    Set
  GreatestRootSequence P a =
    (n : Nat) ->
    Positive n ->
    IsRoot reals (P n) (a n)
    and
    ((x : R) ->
      IsRoot reals (P n) x ->
      lessOrEqual reals x (a n))

  StrictlyIncreasingFromOne :
    (Nat -> R) ->
    Set
  StrictlyIncreasingFromOne a =
    (i j : Nat) ->
    Positive i ->
    NatStrictLess i j ->
    StrictLess reals (a i) (a j)

  proposition :
    (Nat -> Polynomial R) ->
    (Nat -> R) ->
    Set
  proposition P a =
    PolynomialRecurrence P ->
    GreatestRootSequence P a ->
    StrictlyIncreasingFromOne a
    and
    ConvergesTo reals a (zeroR reals)

putnam-1978-b3 : Set1
putnam-1978-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (P : Nat -> Polynomial R) ->
  (a : Nat -> R) ->
  Putnam1978B3Statement.proposition reals P a
