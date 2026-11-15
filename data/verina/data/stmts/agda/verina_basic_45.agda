-- Statement-only formalization of VERINA corpus artifact verina_basic_45,
-- catalog title "findProduct": a deterministic integer-list program multiplies
-- the first even entry by the first odd entry and is connected to its
-- precondition/postcondition correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic45 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infixr 3 _∧_
infix 4 _≤_ _<_ _∈_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data Exists {A : Set} (P : A → Set) : Set where
  witness : (x : A) → P x → Exists P

data IsTrue : Bool → Set where
  true-witness : IsTrue true

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

naturalModTwo : Nat → Nat
naturalModTwo zero = zero
naturalModTwo (suc zero) = suc zero
naturalModTwo (suc (suc n)) = naturalModTwo n

-- Lean remainder modulo positive two is the nonnegative parity remainder.
moduloByTwo : Int → Int
moduloByTwo (pos n) = pos (naturalModTwo n)
moduloByTwo (negsuc n) = pos (naturalModTwo (suc n))

zeroInt : Int
zeroInt = pos zero

isEven : Int → Bool
isEven n = intEqual (moduloByTwo n) zeroInt

isOdd : Int → Bool
isOdd n = notBool (intEqual (moduloByTwo n) zeroInt)

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

intMultiply : Int → Int → Int
intMultiply (pos m) (pos n) = pos (m * n)
intMultiply (pos m) (negsuc n) = negative (m * suc n)
intMultiply (negsuc m) (pos n) = negative (suc m * n)
intMultiply (negsuc m) (negsuc n) = pos (suc m * suc n)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there :
    {y : A} {xs : List A} →
    x ∈ xs →
    x ∈ (y ∷ xs)

record NatPair : Set where
  constructor pair
  field
    pairFirst : Nat
    pairSecond : Nat

open NatPair

findFirstIndexFrom :
  (Int → Bool) → Nat → List Int → Maybe Nat
findFirstIndexFrom predicate index [] = nothing
findFirstIndexFrom predicate index (x ∷ xs) =
  if predicate x
  then just index
  else findFirstIndexFrom predicate (suc index) xs

findFirstIndex : (Int → Bool) → List Int → Maybe Nat
findFirstIndex predicate xs =
  findFirstIndexFrom predicate zero xs

firstEvenOddIndices : List Int → Maybe NatPair
firstEvenOddIndices xs
  with findFirstIndex isEven xs | findFirstIndex isOdd xs
... | just evenIndex | just oddIndex =
  just (pair evenIndex oddIndex)
... | just evenIndex | nothing = nothing
... | nothing | just oddIndex = nothing
... | nothing | nothing = nothing

one : Nat
one = suc zero

findProduct-precond : List Int → Set
findProduct-precond xs =
  (one < listLength xs) ∧
  Exists (λ x → (x ∈ xs) ∧ IsTrue (isEven x)) ∧
  Exists (λ x → (x ∈ xs) ∧ IsTrue (isOdd x))

findProduct :
  (xs : List Int) →
  findProduct-precond xs →
  Int
findProduct xs h-precond with firstEvenOddIndices xs
... | just indices =
  intMultiply
    (nthDefault zeroInt (pairFirst indices) xs)
    (nthDefault zeroInt (pairSecond indices) xs)
... | nothing = zeroInt

findProduct-postcond :
  (xs : List Int) →
  (result : Int) →
  findProduct-precond xs →
  Set
findProduct-postcond xs result h-precond
  with firstEvenOddIndices xs
... | just indices =
  result ≡
    intMultiply
      (nthDefault zeroInt (pairFirst indices) xs)
      (nthDefault zeroInt (pairSecond indices) xs)
... | nothing = Top

findProduct-spec-satisfied : Set
findProduct-spec-satisfied =
  (xs : List Int) →
  (h-precond : findProduct-precond xs) →
  findProduct-postcond
    xs
    (findProduct xs h-precond)
    h-precond
