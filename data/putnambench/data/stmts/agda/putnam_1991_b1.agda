-- Statement-only formalization of PutnamBench corpus artifact putnam_1991_b1:
-- a positive-integer square-remainder recurrence is eventually constant
-- exactly when its initial value is a perfect square. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=N_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

GreatestSquareRootFunction : (Nat -> Nat) -> Set
GreatestSquareRootFunction m =
  (n : Nat) ->
  ((m n * m n) <=N n)
  and
  ((r : Nat) ->
    (r * r) <=N n ->
    r <=N m n)

SquareRemainderFunction :
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Set
SquareRemainderFunction m S =
  (n : Nat) ->
  S n == n - (m n * m n)

FollowsRecurrence :
  Nat ->
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Set
FollowsRecurrence A S a =
  a zero == A
  and
  ((k : Nat) ->
    a (suc k) == a k + S (a k))

EventuallyConstant : (Nat -> Nat) -> Set
EventuallyConstant a =
  Exists Nat
    (\ cutoff ->
      Exists Nat
        (\ constant ->
          (k : Nat) ->
          cutoff <=N k ->
          a k == constant))

PerfectSquare : Nat -> Set
PerfectSquare A =
  Exists Nat
    (\ root ->
      A == root * root)

putnam-1991-b1 : Set
putnam-1991-b1 =
  (m S : Nat -> Nat) ->
  (A : Nat) ->
  (a : Nat -> Nat) ->
  GreatestSquareRootFunction m ->
  SquareRemainderFunction m S ->
  FollowsRecurrence A S a ->
  Positive A ->
  Iff
    (EventuallyConstant a)
    (PerfectSquare A)
