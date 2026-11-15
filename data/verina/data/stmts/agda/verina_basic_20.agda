-- Statement-only formalization of VERINA corpus artifact verina_basic_20,
-- catalog title "uniqueProduct": a deterministic integer-array scan multiplies
-- each distinct value once using seen-set state and is connected to the
-- duplicate-erasure fold correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic20 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

intMultiply : Int → Int → Int
intMultiply (pos m) (pos n) = pos (m * n)
intMultiply (pos m) (negsuc n) = negative (m * suc n)
intMultiply (negsuc m) (pos n) = negative (suc m * n)
intMultiply (negsuc m) (negsuc n) = pos (suc m * suc n)

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intPredecessor : Int → Int
intPredecessor (pos zero) = negsuc zero
intPredecessor (pos (suc n)) = pos n
intPredecessor (negsuc n) = negsuc (suc n)

intAdd : Int → Int → Int
intAdd x (pos zero) = x
intAdd x (pos (suc n)) =
  intSuccessor (intAdd x (pos n))
intAdd x (negsuc zero) = intPredecessor x
intAdd x (negsuc (suc n)) =
  intPredecessor (intAdd x (negsuc n))

intNegate : Int → Int
intNegate (pos zero) = pos zero
intNegate (pos (suc n)) = negsuc n
intNegate (negsuc n) = pos (suc n)

intSubtract : Int → Int → Int
intSubtract x y = intAdd x (intNegate y)

zeroInt : Int
zeroInt = pos zero

oneInt : Int
oneInt = pos (suc zero)

Array : Set → Set
Array A = List A

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

uniqueProduct-loop : Array Int → List Int → Int → Int
uniqueProduct-loop [] seen product = product
uniqueProduct-loop (x ∷ xs) seen product =
  if containsInt x seen
  then uniqueProduct-loop xs seen product
  else
    uniqueProduct-loop
      xs
      (x ∷ seen)
      (intMultiply product x)

uniqueProduct-precond : Array Int → Set
uniqueProduct-precond arr = Top

uniqueProduct :
  (arr : Array Int) →
  uniqueProduct-precond arr →
  Int
uniqueProduct arr h-precond =
  uniqueProduct-loop arr [] oneInt

eraseDups : List Int → List Int
eraseDups [] = []
eraseDups (x ∷ xs) =
  if containsInt x xs
  then eraseDups xs
  else (x ∷ eraseDups xs)

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

uniqueProduct-reference : Array Int → Int
uniqueProduct-reference arr =
  foldLeft intMultiply oneInt (eraseDups arr)

uniqueProduct-postcond :
  (arr : Array Int) →
  (result : Int) →
  uniqueProduct-precond arr →
  Set
uniqueProduct-postcond arr result h-precond =
  (intSubtract result (uniqueProduct-reference arr) ≡ zeroInt) ∧
  (intSubtract (uniqueProduct-reference arr) result ≡ zeroInt)

uniqueProduct-spec-satisfied : Set
uniqueProduct-spec-satisfied =
  (arr : Array Int) →
  (h-precond : uniqueProduct-precond arr) →
  uniqueProduct-postcond
    arr
    (uniqueProduct arr h-precond)
    h-precond
