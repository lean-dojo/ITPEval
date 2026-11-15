-- Statement-only formalization of PutnamBench corpus artifact putnam_2016_a2
-- (putnambench__agda__putnam_2016_a2): the limit of the largest positive
-- integer selected by a binomial-coefficient inequality is (3 + sqrt 5) / 2.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2016A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _!=_ _<=N_ _<N_
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

data _<N_ : Nat -> Nat -> Set where
  zero<N   : {n : Nat} -> zero <N suc n
  suc<sucN : {m n : Nat} -> m <N n -> suc m <N suc n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

fiveN : Nat
fiveN =
  suc (suc threeN)

choose : Nat -> Nat -> Nat
choose n zero =
  oneN
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n (suc k) + choose n k

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
        (\ n -> lessOrEqual x (fromNat n))
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

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

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

record StandardSquareRoot
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    squareRoot : R -> R

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual reals (zeroR reals) (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      square reals (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual reals x (zeroR reals) ->
      squareRoot x == zeroR reals
    square-root-unique :
      (x y : R) ->
      lessOrEqual reals (zeroR reals) y ->
      square reals y == x ->
      squareRoot x == y

open StandardSquareRoot

Qualifies : Nat -> Nat -> Set
Qualifies n m =
  Positive m
  and
  choose (m - oneN) n <N choose m (n - oneN)

GreatestQualifying : Nat -> Nat -> Set
GreatestQualifying n greatest =
  Qualifies n greatest
  and
  ((m : Nat) ->
    Qualifies n m ->
    m <=N greatest)

DefinesM : (Nat -> Nat) -> Set
DefinesM M =
  (n : Nat) ->
  Positive n ->
  GreatestQualifying n (M n)

module Putnam2016A2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (roots : StandardSquareRoot reals) where

  solution : R
  solution =
    divide reals
      (add reals
        (fromNat reals threeN)
        (squareRoot roots (fromNat reals fiveN)))
      (fromNat reals twoN)

  ratio : (Nat -> Nat) -> Nat -> R
  ratio M n =
    divide reals
      (fromNat reals (M n))
      (fromNat reals n)

  proposition : Set
  proposition =
    (M : Nat -> Nat) ->
    DefinesM M ->
    ConvergesTo reals (ratio M) solution

putnam-2016-a2 : Set1
putnam-2016-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (roots : StandardSquareRoot reals) ->
  Putnam2016A2Statement.proposition reals roots
