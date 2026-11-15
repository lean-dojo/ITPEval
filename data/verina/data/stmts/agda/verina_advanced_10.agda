-- Statement-only formalization of VERINA corpus artifact verina_advanced_10,
-- catalog title "findExponents": a deterministic program computes the exponent
-- of each supplied prime in a positive natural number's factorization.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced10 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infixr 2 _∨_
infixr 3 _∧_
infix 4 _≤_ _<_ _∈_ _∣_
infixr 5 _&&_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

one : Nat
one = suc zero

two : Nat
two = suc one

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

record NatPair : Set where
  constructor pair
  field
    pairFirst : Nat
    pairSecond : Nat

open NatPair public

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) = predicate x ∧ All predicate xs

data _∈_ (x : Nat) : List Nat → Set where
  here : {xs : List Nat} → x ∈ (x ∷ xs)
  there : {y : Nat} {xs : List Nat} → x ∈ xs → x ∈ (y ∷ xs)

NoDuplicates : List Nat → Set
NoDuplicates [] = Top
NoDuplicates (x ∷ xs) = Not (x ∈ xs) ∧ NoDuplicates xs

record _∣_ (divisor dividend : Nat) : Set where
  constructor divides
  field
    quotient : Nat
    divisionEquation : dividend ≡ divisor * quotient

record Prime (p : Nat) : Set where
  constructor prime
  field
    atLeastTwo : two ≤ p
    onlyTrivialDivisors :
      (d : Nat) → d ∣ p → (d ≡ one) ∨ (d ≡ p)

removePrimeFactorWithFuel : Nat → Nat → Nat → Nat
removePrimeFactorWithFuel zero current p = current
removePrimeFactorWithFuel (suc fuel) current p =
  if natLess one p && natLess zero current
  then
    if natEqual (naturalMod current p) zero
    then
      removePrimeFactorWithFuel fuel (naturalDiv current p) p
    else current
  else current

removePrimeFactor : Nat → Nat → Nat
removePrimeFactor n p = removePrimeFactorWithFuel n n p

removeAllPrimeFactors : Nat → List Nat → Nat
removeAllPrimeFactors n primes =
  foldLeft removePrimeFactor n primes

FindExponents-precond : Nat → List Nat → Set
FindExponents-precond n primes =
  (zero < n) ∧
  ((zero < listLength primes) ∧
  ((All Prime primes) ∧
  ((NoDuplicates primes) ∧
  (removeAllPrimeFactors n primes ≡ one))))

countFactorWithFuel : Nat → Nat → Nat → Nat → NatPair
countFactorWithFuel zero current p count = pair count current
countFactorWithFuel (suc fuel) zero p count = pair count zero
countFactorWithFuel (suc fuel) (suc n) p count =
  if natLess one p
  then
    if natEqual (naturalMod (suc n) p) zero
    then
      countFactorWithFuel
        fuel
        (naturalDiv (suc n) p)
        p
        (suc count)
    else pair count (suc n)
  else pair count (suc n)

countFactor : Nat → Nat → Nat → NatPair
countFactor n p count = countFactorWithFuel n n p count

countFactors : Nat → List Nat → List NatPair
countFactors n [] = []
countFactors n (p ∷ ps) =
  let counted = countFactor n p zero
  in pair p (pairFirst counted) ∷
     countFactors (pairSecond counted) ps

findExponents :
  (n : Nat) →
  (primes : List Nat) →
  FindExponents-precond n primes →
  List NatPair
findExponents n primes h-precond = countFactors n primes

power : Nat → Nat → Nat
power base zero = one
power base (suc exponent) = base * power base exponent

multiplyPrimePower : Nat → NatPair → Nat
multiplyPrimePower accumulator factor =
  accumulator * power (pairFirst factor) (pairSecond factor)

resultProduct : List NatPair → Nat
resultProduct result = foldLeft multiplyPrimePower one result

resultPrimes : List NatPair → List Nat
resultPrimes result = mapList pairFirst result

FindExponents-postcond :
  (n : Nat) →
  (primes : List Nat) →
  (result : List NatPair) →
  FindExponents-precond n primes →
  Set
FindExponents-postcond n primes result h-precond =
  (n ≡ resultProduct result) ∧
  ((All (λ factor → pairFirst factor ∈ primes) result) ∧
  (All (λ p → p ∈ resultPrimes result) primes))

FindExponents-spec-satisfied : Set
FindExponents-spec-satisfied =
  (n : Nat) →
  (primes : List Nat) →
  (h-precond : FindExponents-precond n primes) →
  FindExponents-postcond
    n
    primes
    (findExponents n primes h-precond)
    h-precond
