-- Statement-only formalization of PutnamBench corpus artifact putnam_1965_b4:
-- the binomial-sum quotient satisfies a rational recurrence, converges exactly
-- for nonnegative real inputs, and then tends to the square root. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

halfFloor : Nat -> Nat
halfFloor zero =
  zero
halfFloor (suc zero) =
  zero
halfFloor (suc (suc n)) =
  suc (halfFloor n)

choose : Nat -> Nat -> Nat
choose n zero =
  oneN
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n (suc k) + choose n k

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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

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

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals (subtract reals center radius) x
  and
  StrictLess reals x (add reals center radius)

naturalPower :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

sumThrough :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
sumThrough reals zero term =
  term zero
sumThrough reals (suc n) term =
  add reals
    (sumThrough reals n term)
    (term (suc n))

ConvergesTo :
  {R : Set} ->
  CompleteOrderedField R ->
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
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    squareRoot : R -> R

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      lessOrEqual reals (zeroR reals) (squareRoot x)

    square-root-square :
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      multiply reals (squareRoot x) (squareRoot x) == x

open StandardSquareRoot

module Putnam1965B4Statement
  {R : Set}
  (reals : CompleteOrderedField R)
  (roots : StandardSquareRoot reals) where

  evenSum : Nat -> R -> R
  evenSum n x =
    sumThrough reals
      (halfFloor n)
      (\ i ->
        multiply reals
          (fromNat reals (choose n (twoN * i)))
          (naturalPower reals x i))

  oddSum : Nat -> R -> R
  oddSum n x =
    sumThrough reals
      (halfFloor (n - oneN))
      (\ i ->
        multiply reals
          (fromNat reals (choose n (twoN * i + oneN)))
          (naturalPower reals x i))

  proposition : Set
  proposition =
    (f u v : Nat -> R -> R) ->
    ((n : Nat) ->
      Positive n ->
      (x : R) ->
      u n x == evenSum n x) ->
    ((n : Nat) ->
      Positive n ->
      (x : R) ->
      v n x == oddSum n x) ->
    ((n : Nat) ->
      Positive n ->
      (x : R) ->
      f n x == divide reals (u n x) (v n x)) ->
    (n : Nat) ->
    Positive n ->
    (((x : R) ->
      v n x != zeroR reals ->
      v (suc n) x != zeroR reals ->
      add reals (f n x) (oneR reals) != zeroR reals ->
      f (suc n) x ==
      divide reals
        (add reals (f n x) x)
        (add reals (f n x) (oneR reals)))
    and
    ((x : R) ->
      Iff
        (lessOrEqual reals (zeroR reals) x)
        (Exists R
          (\ limit ->
            ConvergesTo reals
              (\ m -> f m x)
              limit)))
    and
    ((x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      ConvergesTo reals
        (\ m -> f m x)
        (squareRoot roots x)))

putnam-1965-b4 : Set1
putnam-1965-b4 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (roots : StandardSquareRoot reals) ->
  Putnam1965B4Statement.proposition reals roots
