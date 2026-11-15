-- Statement-only formalization of PutnamBench corpus artifact putnam_1980_b6:
-- the reduced denominator of the recursively defined rational value G(d,p)
-- is not divisible by the prime p when 1 < d <= p. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper; mod-helper)

infix 4 _<=N_ _<N_ _~Q_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

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

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

record Pair (A B : Set) : Set where
  constructor pair
  field
    first-coordinate  : A
    second-coordinate : B

pred : Nat -> Nat
pred zero =
  zero
pred (suc n) =
  n

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

scaleInt : Int -> Nat -> Int
scaleInt z n =
  multiplyInt z (pos n)

absInt : Int -> Nat
absInt (pos n) =
  n
absInt (negsuc n) =
  suc n

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator q =
  suc (denominator-minus-one q)

_~Q_ : Rational -> Rational -> Set
x ~Q y =
  scaleInt (numerator x) (denominator y) ==
  scaleInt (numerator y) (denominator x)

zeroQ : Rational
zeroQ =
  fraction (pos zero) zero

addQ : Rational -> Rational -> Rational
addQ x y =
  fraction
    (addInt
      (scaleInt (numerator x) (denominator y))
      (scaleInt (numerator y) (denominator x)))
    (pred (denominator x * denominator y))

multiplyQ : Rational -> Rational -> Rational
multiplyQ x y =
  fraction
    (multiplyInt (numerator x) (numerator y))
    (pred (denominator x * denominator y))

naturalRatio : Nat -> Nat -> Rational
naturalRatio numerator-value denominator-value =
  fraction
    (pos numerator-value)
    (pred denominator-value)

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator-value zero =
  zero
naturalDiv numerator-value (suc denominator-value) =
  div-helper
    zero
    denominator-value
    numerator-value
    denominator-value

naturalMod : Nat -> Nat -> Nat
naturalMod numerator-value zero =
  zero
naturalMod numerator-value (suc denominator-value) =
  mod-helper
    zero
    denominator-value
    numerator-value
    denominator-value

gcdWithFuel : Nat -> Nat -> Nat -> Nat
gcdWithFuel zero a b =
  a
gcdWithFuel (suc fuel) a zero =
  a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

naturalGCD : Nat -> Nat -> Nat
naturalGCD a b =
  gcdWithFuel (suc (a + b)) a b

reducedDenominator : Rational -> Nat
reducedDenominator q =
  naturalDiv
    (denominator q)
    (naturalGCD (absInt (numerator q)) (denominator q))

Divides : Nat -> Nat -> Set
Divides divisor number =
  Exists Nat
    (\ factor -> divisor * factor == number)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

Prime : Nat -> Set
Prime number =
  twoN <=N number
  and
  ((divisor : Nat) ->
    Divides divisor number ->
    divisor == oneN or divisor == number)

oneZ : Int
oneZ =
  pos oneN

sumFrom :
  Nat ->
  Nat ->
  (Nat -> Rational) ->
  Rational
sumFrom start zero term =
  zeroQ
sumFrom start (suc count) term =
  addQ
    (sumFrom start count term)
    (term (start + count))

sumInclusive :
  Nat ->
  Nat ->
  (Nat -> Rational) ->
  Rational
sumInclusive lower upper term =
  sumFrom lower (suc upper - lower) term

Recurrence :
  (Pair Int Int -> Rational) ->
  Set
Recurrence G =
  (d n : Nat) ->
  d <=N n ->
  ((d == oneN ->
    G (pair (pos d) (pos n)) ~Q
    naturalRatio oneN n)
  and
  (oneN <N d ->
    G (pair (pos d) (pos n)) ~Q
    multiplyQ
      (naturalRatio d n)
      (sumInclusive d n
        (\ i ->
          G
            (pair
              (subtractInt (pos d) oneZ)
              (subtractInt (pos i) oneZ))))))

putnam-1980-b6 : Set
putnam-1980-b6 =
  (G : Pair Int Int -> Rational) ->
  Recurrence G ->
  (d p : Nat) ->
  (oneN <N d and d <=N p and Prime p) ->
  Not
    (Divides p
      (reducedDenominator
        (G (pair (pos d) (pos p)))))
