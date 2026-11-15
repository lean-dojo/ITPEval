-- Statement-only formalization of VERINA corpus artifact verina_basic_62,
-- catalog title "Find": a deterministic linear search of an integer array
-- returns the first index containing the key or negative one and is connected
-- to its complete first-occurrence correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic62 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 2 _∨_
infixr 3 _∧_
infix 4 _≤_ _<_

record Top : Set where
  constructor top

data Empty : Set where

Not : Set → Set
Not A = A → Empty

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

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

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess x y = boolNot (intLessOrEqual y x)

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

IntLess : Int → Int → Set
IntLess x y = IsTrue (intLess x y)

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

zeroInt : Int
zeroInt = pos zero

negativeOne : Int
negativeOne = negsuc zero

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

Find-precond : Array Int → Int → Set
Find-precond a key = Top

Find-loop : Array Int → Nat → Int → Int
Find-loop [] index key = negativeOne
Find-loop (x ∷ xs) index key =
  if intEqual x key
  then pos index
  else Find-loop xs (suc index) key

Find :
  (a : Array Int) →
  (key : Int) →
  Find-precond a key →
  Int
Find a key h-precond =
  Find-loop a zero key

Find-postcond :
  (a : Array Int) →
  (key : Int) →
  (result : Int) →
  Find-precond a key →
  Set
Find-postcond a key result h-precond =
  ((result ≡ negativeOne) ∨
    (IntLessOrEqual zeroInt result ∧
     IntLess result (pos (arraySize a)))) ∧
  (Not (result ≡ negativeOne) →
    (indexDefault zeroInt a (intToNat result) ≡ key) ∧
    ((i : Nat) →
      i < intToNat result →
      Not (indexDefault zeroInt a i ≡ key))) ∧
  (result ≡ negativeOne →
    (i : Nat) →
    i < arraySize a →
    Not (indexDefault zeroInt a i ≡ key))

Find-spec-satisfied : Set
Find-spec-satisfied =
  (a : Array Int) →
  (key : Int) →
  (h-precond : Find-precond a key) →
  Find-postcond
    a
    key
    (Find a key h-precond)
    h-precond
