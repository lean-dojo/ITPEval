-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__093, "The Birthday Problem": collision assignments
-- are a strict majority for 23 people and a strict minority for 22 people
-- when birthdays range over 365 days. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<N_

record Both (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _<N_ : Nat -> Nat -> Set where
  zero<N-suc : {n : Nat} -> zero <N suc n
  suc<N-suc : {m n : Nat} -> m <N n -> suc m <N suc n

power : Nat -> Nat -> Nat
power base zero = suc zero
power base (suc exponent) = base * power base exponent

subtract : Nat -> Nat -> Nat
subtract n zero = n
subtract zero (suc m) = zero
subtract (suc n) (suc m) = subtract n m

assignmentCount : Nat -> Nat -> Nat
assignmentCount people days = power days people

injectiveAssignmentCount : Nat -> Nat -> Nat
injectiveAssignmentCount zero days = suc zero
injectiveAssignmentCount (suc people) zero = zero
injectiveAssignmentCount (suc people) (suc days) =
  suc days * injectiveAssignmentCount people days

collisionAssignmentCount : Nat -> Nat -> Nat
collisionAssignmentCount people days =
  subtract
    (assignmentCount people days)
    (injectiveAssignmentCount people days)

birthday-problem : Set
birthday-problem =
  Both
    (assignmentCount 23 365 <N
      2 * collisionAssignmentCount 23 365)
    (2 * collisionAssignmentCount 22 365 <N
      assignmentCount 22 365)
