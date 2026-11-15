-- Statement-only formalization of VERINA corpus artifact verina_basic_67,
-- catalog title "IsPalindrome": a deterministic character-list program compares
-- mirrored positions and is connected to its all-index palindrome correctness
-- contract with no precondition. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic67 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primCharEquality; primNatToChar)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 2 _↔_
infix 4 _≤_ _<_

record Top : Set where
  constructor top

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

listIndex : {A : Set} → Nat → List A → Maybe A
listIndex zero [] = nothing
listIndex zero (x ∷ xs) = just x
listIndex (suc n) [] = nothing
listIndex (suc n) (_ ∷ xs) = listIndex n xs

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

nullChar : Char
nullChar = primNatToChar zero

IsPalindrome-precond : List Char → Set
IsPalindrome-precond x = Top

isPalindromeHelperFuel :
  Nat →
  List Char →
  Nat →
  Nat →
  Bool
isPalindromeHelperFuel zero x i j = true
isPalindromeHelperFuel (suc fuel) x i j with natLess i j
... | false = true
... | true with listIndex i x | listIndex j x
...   | just ci | just cj =
  if primCharEquality ci cj
  then
    isPalindromeHelperFuel
      fuel
      x
      (suc i)
      (predecessor j)
  else false
...   | _ | _ = false

-- The initial fuel is exact: whenever i < j, the recursive source call changes
-- j to j - 1 while one fuel constructor is consumed.
isPalindromeHelper : List Char → Nat → Nat → Bool
isPalindromeHelper x i j =
  isPalindromeHelperFuel (suc j) x i j

IsPalindrome :
  (x : List Char) →
  IsPalindrome-precond x →
  Bool
IsPalindrome x h-precond with natEqual (listLength x) zero
... | true = true
... | false =
  isPalindromeHelper
    x
    zero
    (natSubtract (listLength x) (suc zero))

IsPalindrome-postcond :
  (x : List Char) →
  (result : Bool) →
  IsPalindrome-precond x →
  Set
IsPalindrome-postcond x result h-precond =
  IsTrue result ↔
  ((i : Nat) →
    i < listLength x →
    indexDefault nullChar x i ≡
    indexDefault
      nullChar
      x
      (natSubtract
        (natSubtract (listLength x) i)
        (suc zero)))

IsPalindrome-spec-satisfied : Set
IsPalindrome-spec-satisfied =
  (x : List Char) →
  (h-precond : IsPalindrome-precond x) →
  IsPalindrome-postcond
    x
    (IsPalindrome x h-precond)
    h-precond
