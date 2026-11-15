-- Statement-only formalization of PutnamBench corpus artifact putnam_1999_b6
-- (putnambench__agda__putnam_1999_b6): a finite set of integers greater than
-- one satisfying a universal gcd dichotomy contains two elements whose gcd
-- is prime. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _member_ _<=N_ _divides_
infixr 3 _and_
infixr 2 _or_

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

data _member_ {A : Set} (x : A) : List A -> Set where
  here  : {xs : List A} -> x member (x ∷ xs)
  there : {y : A} {xs : List A} ->
          x member xs ->
          x member (y ∷ xs)

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : dividend == divisor * quotient

data IntegerGreaterThanOne : Int -> Set where
  positive-at-least-two :
    (k : Nat) ->
    IntegerGreaterThanOne (pos (suc (suc k)))

absInt : Int -> Nat
absInt (pos n) =
  n
absInt (negsuc n) =
  suc n

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

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

integerGCD : Int -> Int -> Nat
integerGCD x y =
  naturalGCD (absInt x) (absInt y)

record Prime (p : Nat) : Set where
  field
    at-least-two :
      suc (suc zero) <=N p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == suc zero) or (d == p)

putnam-1999-b6 : Set
putnam-1999-b6 =
  (S : List Int) ->
  ((s : Int) ->
    s member S ->
    IntegerGreaterThanOne s) ->
  ((n : Int) ->
    Exists Int
      (\ s ->
        s member S
        and
        ((integerGCD s n == suc zero)
        or
        (integerGCD s n == absInt s)))) ->
  Exists Int
    (\ s ->
      s member S
      and
      Exists Int
        (\ t ->
          t member S
          and
          Prime (integerGCD s t)))
