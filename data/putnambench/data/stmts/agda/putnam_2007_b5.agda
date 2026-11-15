-- Statement-only formalization of PutnamBench corpus artifact putnam_2007_b5
-- (putnambench__agda__putnam_2007_b5): positive k admits k real
-- polynomials expressing floor(n/k)^k in lower powers of floor(n/k) for
-- every integer n. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2007B5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
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
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

intSuccessor : Int -> Int
intSuccessor (pos n) =
  pos (suc n)
intSuccessor (negsuc zero) =
  pos zero
intSuccessor (negsuc (suc n)) =
  negsuc n

embedInt :
  {R : Set} ->
  (Nat -> R) ->
  (R -> R) ->
  Int ->
  R
embedInt fromNatural negateR (pos n) =
  fromNatural n
embedInt fromNatural negateR (negsuc n) =
  negateR (fromNatural (suc n))

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R
    floor : R -> Int

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

    floor-lower :
      (x : R) ->
      lessOrEqual
        (embedInt fromNat negate (floor x))
        x
    floor-upper :
      (x : R) ->
      lessOrEqual
        x
        (embedInt fromNat negate (intSuccessor (floor x)))
      and
      x != embedInt fromNat negate (intSuccessor (floor x))

open CompleteOrderedRealField

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals =
  embedInt (fromNat reals) (negate reals)

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
naturalPower reals x (suc exponent) =
  multiply reals
    (naturalPower reals x exponent)
    x

Polynomial : Set -> Set
Polynomial R =
  List R

evaluatePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  R
evaluatePolynomial reals [] x =
  zeroR reals
evaluatePolynomial reals (coefficient ∷ coefficients) x =
  add reals
    coefficient
    (multiply reals
      x
      (evaluatePolynomial reals coefficients x))

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {count : Nat} ->
  (Fin count -> R) ->
  R
sumFin reals {zero} term =
  zeroR reals
sumFin reals {suc count} term =
  add reals
    (term fzero)
    (sumFin reals (\ i -> term (fsuc i)))

module Putnam2007B5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  floorQuotient :
    Nat ->
    Int ->
    Int
  floorQuotient k n =
    floor reals
      (divide reals
        (fromInt reals n)
        (fromNat reals k))

  IdentityFor :
    (k : Nat) ->
    (Fin k -> Polynomial R) ->
    Int ->
    Set
  IdentityFor k polynomials n =
    let
      quotient = fromInt reals (floorQuotient k n)
      argument = fromInt reals n
    in
    naturalPower reals quotient k
    ==
    sumFin reals
      (\ i ->
        multiply reals
          (evaluatePolynomial reals (polynomials i) argument)
          (naturalPower reals quotient (finToNat i)))

  proposition : Set
  proposition =
    (k : Nat) ->
    Positive k ->
    Exists (Fin k -> Polynomial R)
      (\ polynomials ->
        (n : Int) ->
        IdentityFor k polynomials n)

putnam-2007-b5 : Set1
putnam-2007-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2007B5Statement.proposition reals
