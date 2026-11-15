-- Statement-only formalization of VERINA corpus artifact verina_basic_7,
-- catalog title "sumOfSquaresOfFirstNOddNumbers": a deterministic natural-number
-- countdown program sums the squares of the first n odd numbers and is connected
-- to its closed-form correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic7 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

naturalDivThree : Nat → Nat
naturalDivThree zero = zero
naturalDivThree (suc zero) = zero
naturalDivThree (suc (suc zero)) = zero
naturalDivThree (suc (suc (suc n))) =
  suc (naturalDivThree n)

oddSquare : Nat → Nat
oddSquare k =
  let odd = natSubtract (two * k) one
  in odd * odd

sumOfSquaresOfFirstNOddNumbers-loop : Nat → Nat → Nat
sumOfSquaresOfFirstNOddNumbers-loop zero sum = sum
sumOfSquaresOfFirstNOddNumbers-loop (suc k) sum =
  sumOfSquaresOfFirstNOddNumbers-loop
    k
    (sum + oddSquare (suc k))

sumOfSquaresOfFirstNOddNumbers-precond : Nat → Set
sumOfSquaresOfFirstNOddNumbers-precond n = Top

sumOfSquaresOfFirstNOddNumbers :
  (n : Nat) →
  sumOfSquaresOfFirstNOddNumbers-precond n →
  Nat
sumOfSquaresOfFirstNOddNumbers n h-precond =
  sumOfSquaresOfFirstNOddNumbers-loop n zero

sumOfSquaresClosedForm : Nat → Nat
sumOfSquaresClosedForm n =
  naturalDivThree
    ((n * natSubtract (two * n) one) * ((two * n) + one))

sumOfSquaresOfFirstNOddNumbers-postcond :
  (n result : Nat) →
  sumOfSquaresOfFirstNOddNumbers-precond n →
  Set
sumOfSquaresOfFirstNOddNumbers-postcond n result h-precond =
  (natSubtract result (sumOfSquaresClosedForm n) ≡ zero) ∧
  (natSubtract (sumOfSquaresClosedForm n) result ≡ zero)

sumOfSquaresOfFirstNOddNumbers-spec-satisfied : Set
sumOfSquaresOfFirstNOddNumbers-spec-satisfied =
  (n : Nat) →
  (h-precond : sumOfSquaresOfFirstNOddNumbers-precond n) →
  sumOfSquaresOfFirstNOddNumbers-postcond
    n
    (sumOfSquaresOfFirstNOddNumbers n h-precond)
    h-precond
