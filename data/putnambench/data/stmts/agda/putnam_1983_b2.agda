-- Statement-only formalization of PutnamBench corpus artifact putnam_1983_b2:
-- the number of representations of each positive natural as a sum of powers
-- of two, using each power at most three times, is the floor of one real
-- polynomial evaluated at that natural. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinalityUpTo
  {A : Set}
  (_~_ : A -> A -> Set)
  (P : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin cardinality)
        (\ index -> x ~ enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index ~ enumerate right-index ->
      left-index == right-index

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

powerNat : Nat -> Nat -> Nat
powerNat base zero =
  oneN
powerNat base (suc exponent) =
  base * powerNat base exponent

sumFirst : Nat -> (Nat -> Nat) -> Nat
sumFirst zero term =
  zero
sumFirst (suc count) term =
  sumFirst count term + term count

Multiplicity : Set
Multiplicity =
  Nat -> Nat

PointwiseEqual : Multiplicity -> Multiplicity -> Set
PointwiseEqual firstMultiplicity secondMultiplicity =
  (m : Nat) ->
  firstMultiplicity m == secondMultiplicity m

PowersOfTwoOnly : Multiplicity -> Set
PowersOfTwoOnly multiplicity =
  (m : Nat) ->
  Positive (multiplicity m) ->
  Exists Nat
    (\ exponent ->
      m == powerNat twoN exponent)

MultiplicityAtMostThree : Multiplicity -> Set
MultiplicityAtMostThree multiplicity =
  (m : Nat) ->
  multiplicity m <=N threeN

FiniteSumEquals : Multiplicity -> Nat -> Set
FiniteSumEquals multiplicity n =
  Exists Nat
    (\ cutoff ->
      (((m : Nat) ->
        cutoff <=N m ->
        multiplicity m == zero)
      and
      (sumFirst cutoff
        (\ m -> m * multiplicity m)
        == n)))

AdmissibleMultiset : Nat -> Multiplicity -> Set
AdmissibleMultiset n multiplicity =
  PowersOfTwoOnly multiplicity
  and
  MultiplicityAtMostThree multiplicity
  and
  FiniteSumEquals multiplicity n

RepresentationCountingFunction : (Nat -> Nat) -> Set
RepresentationCountingFunction f =
  (n : Nat) ->
  HasCardinalityUpTo
    PointwiseEqual
    (AdmissibleMultiset n)
    (f n)

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

module Putnam1983B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  PolynomialMatches :
    (Nat -> Nat) ->
    Polynomial R ->
    Set
  PolynomialMatches f polynomial =
    (n : Nat) ->
    Positive n ->
    floor reals
      (evaluatePolynomial reals
        polynomial
        (fromNat reals n))
    ==
    pos (f n)

  proposition : Set
  proposition =
    (f : Nat -> Nat) ->
    RepresentationCountingFunction f ->
    Exists (Polynomial R)
      (PolynomialMatches f)

putnam-1983-b2 : Set1
putnam-1983-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1983B2Statement.proposition reals
