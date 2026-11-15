-- Statement-only formalization of PutnamBench corpus artifact putnam_1981_a5:
-- the polynomial Q(x) = (x^2 + 1)P(x)P'(x) + x(P(x)^2 + P'(x)^2)
-- has at least 2n - 1 distinct real roots when P has n distinct real roots
-- greater than 1. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
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

record Top : Set where
  constructor truth

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

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
  add reals
    coefficient
    (multiply reals x (evaluate reals coefficients x))

derivativeValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  R
derivativeValue reals [] x =
  zeroR reals
derivativeValue reals (coefficient ∷ coefficients) x =
  add reals
    (evaluate reals coefficients x)
    (multiply reals x
      (derivativeValue reals coefficients x))

record HasCardinality
  {A : Set}
  (P : A -> Set)
  (cardinality : Nat) : Set where
  field
    enumerate :
      Fin cardinality -> A
    enumerated-member :
      (i : Fin cardinality) ->
      P (enumerate i)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin cardinality)
        (\ i -> x == enumerate i)
    enumeration-injective :
      (i j : Fin cardinality) ->
      enumerate i == enumerate j ->
      i == j

FinitePredicate :
  {A : Set} ->
  (A -> Set) ->
  Set
FinitePredicate P =
  Exists Nat (HasCardinality P)

NCardValue :
  {A : Set} ->
  (A -> Set) ->
  Nat ->
  Set
NCardValue P cardinality =
  HasCardinality P cardinality
  or
  (cardinality == zero
    and
    Not (FinitePredicate P))

module Putnam1981A5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  oneN : Nat
  oneN =
    suc zero

  twoN : Nat
  twoN =
    suc oneN

  qValue :
    Polynomial R ->
    R ->
    R
  qValue P x =
    let
      p = evaluate reals P x
      p' = derivativeValue reals P x
    in
    add reals
      (multiply reals
        (add reals
          (square reals x)
          (oneR reals))
        (multiply reals p p'))
      (multiply reals x
        (add reals
          (square reals p)
          (square reals p')))

  RootsAboveOne :
    Polynomial R ->
    R ->
    Set
  RootsAboveOne P x =
    StrictLess reals (oneR reals) x
    and
    evaluate reals P x == zeroR reals

  QRoots :
    Polynomial R ->
    R ->
    Set
  QRoots P x =
    qValue P x == zeroR reals

  AtLeastTwiceMinusOne :
    Nat ->
    Nat ->
    Set
  AtLeastTwiceMinusOne n q-roots =
    lessOrEqual reals
      (subtract reals
        (multiply reals
          (fromNat reals twoN)
          (fromNat reals n))
        (oneR reals))
      (fromNat reals q-roots)

  universal-bound : Set
  universal-bound =
    (P : Polynomial R) ->
    Exists Nat
      (\ n ->
        NCardValue (RootsAboveOne P) n
        and
        Exists Nat
          (\ q-roots ->
            NCardValue (QRoots P) q-roots
            and
            AtLeastTwiceMinusOne n q-roots))

  proposition : Set
  proposition =
    Iff universal-bound Top

putnam-1981-a5 : Set1
putnam-1981-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1981A5Statement.proposition reals
