-- Statement-only formalization of PutnamBench corpus artifact putnam_2015_b4
-- (putnambench__agda__putnam_2015_b4): the sum over positive integer triangle
-- side triples has reduced rational value 17 / 21. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
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

record Divides (divisor dividend : Nat) : Set where
  constructor divides
  field
    quotient : Nat
    product  : divisor * quotient == dividend

RelativelyPrime : Nat -> Nat -> Set
RelativelyPrime m n =
  (d : Nat) ->
  Divides d m ->
  Divides d n ->
  d == suc zero

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
  multiply reals
    (naturalPower reals x n)
    x

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

lessNat : Nat -> Nat -> Bool
lessNat zero zero =
  false
lessNat zero (suc n) =
  true
lessNat (suc m) zero =
  false
lessNat (suc m) (suc n) =
  lessNat m n

andBool : Bool -> Bool -> Bool
andBool true b =
  b
andBool false b =
  false

ifBool :
  {A : Set} ->
  Bool ->
  A ->
  A ->
  A
ifBool true whenTrue whenFalse =
  whenTrue
ifBool false whenTrue whenFalse =
  whenFalse

isTriangle : Nat -> Nat -> Nat -> Bool
isTriangle a b c =
  andBool
    (lessNat a (b + c))
    (andBool
      (lessNat b (c + a))
      (lessNat c (a + b)))

triangleTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Nat ->
  Nat ->
  R
triangleTerm reals a b c =
  ifBool
    (isTriangle a b c)
    (divide reals
      (naturalPower reals (fromNat reals 2) a)
      (multiply reals
        (naturalPower reals (fromNat reals 3) b)
        (naturalPower reals (fromNat reals 5) c)))
    (zeroR reals)

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

cubePartialSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
cubePartialSum reals bound =
  sumFirst reals bound
    (\ i ->
      sumFirst reals bound
        (\ j ->
          sumFirst reals bound
            (\ k ->
              triangleTerm reals
                (suc i)
                (suc j)
                (suc k))))

seventeen : Nat
seventeen =
  17

twentyOne : Nat
twentyOne =
  21

seventeenTwentyFirsts :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
seventeenTwentyFirsts reals =
  divide reals
    (fromNat reals seventeen)
    (fromNat reals twentyOne)

putnam-2015-b4 : Set1
putnam-2015-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  ConvergesTo reals
    (cubePartialSum reals)
    (seventeenTwentyFirsts reals)
  and
  RelativelyPrime seventeen twentyOne
