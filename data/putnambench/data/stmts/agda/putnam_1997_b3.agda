-- Statement-only formalization of PutnamBench corpus artifact putnam_1997_b3:
-- the positive integers whose harmonic sum has reduced denominator not
-- divisible by 5 are exactly four specified intervals. This file contains no
-- proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infix 4 _<=N_
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

record Iff (A B : Set) : Set where
  constructor iff
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

data Positive : Nat -> Set where
  positive : (n : Nat) -> Positive (suc n)

pred : Nat -> Nat
pred zero =
  zero
pred (suc n) =
  n

record Rational : Set where
  constructor fraction
  field
    numerator             : Nat
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator q =
  suc (denominator-minus-one q)

zeroQ : Rational
zeroQ =
  fraction zero zero

addQ : Rational -> Rational -> Rational
addQ x y =
  fraction
    ((numerator x * denominator y)
      + (numerator y * denominator x))
    (pred (denominator x * denominator y))

naturalRatio : Nat -> Nat -> Rational
naturalRatio numerator-value denominator-value =
  fraction numerator-value (pred denominator-value)

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
    (naturalGCD (numerator q) (denominator q))

Divides : Nat -> Nat -> Set
Divides divisor number =
  Exists Nat
    (\ factor -> divisor * factor == number)

oneN : Nat
oneN =
  suc zero

fiveN : Nat
fiveN =
  5

harmonicSum : Nat -> Rational
harmonicSum zero =
  zeroQ
harmonicSum (suc n) =
  addQ
    (harmonicSum n)
    (naturalRatio oneN (suc n))

Between : Nat -> Nat -> Nat -> Set
Between lower upper n =
  lower <=N n and n <=N upper

putnam-1997-b3-solution : Nat -> Set
putnam-1997-b3-solution n =
  Between 1 4 n
  or
  Between 20 24 n
  or
  Between 100 104 n
  or
  Between 120 124 n

putnam-1997-b3 : Set
putnam-1997-b3 =
  (n : Nat) ->
  Positive n ->
  Iff
    (putnam-1997-b3-solution n)
    (Not
      (Divides fiveN
        (reducedDenominator (harmonicSum n))))
