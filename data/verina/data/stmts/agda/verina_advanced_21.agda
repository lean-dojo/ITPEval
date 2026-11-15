-- Statement-only formalization of VERINA corpus artifact verina_advanced_21,
-- catalog title "isPalindrome": a deterministic string program checks matching
-- characters from both ends and equality with the reversed character list.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced21 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primCharEquality)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String; primStringToList)

infixr 3 _∧_
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

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natGreaterOrEqual : Nat → Nat → Bool
natGreaterOrEqual m n = natLessOrEqual n m

one : Nat
one = suc zero

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

listIndex : {A : Set} → Nat → List A → Maybe A
listIndex zero [] = nothing
listIndex zero (x ∷ xs) = just x
listIndex (suc n) [] = nothing
listIndex (suc n) (_ ∷ xs) = listIndex n xs

charactersEqualAt : Nat → Nat → List Char → Bool
charactersEqualAt left right chars
  with listIndex left chars | listIndex right chars
... | just c-left | just c-right = primCharEquality c-left c-right
... | _ | _ = false

checkIndices : Nat → Nat → List Char → Bool
checkIndices left zero chars = true
checkIndices left (suc right) chars =
  if natGreaterOrEqual left (suc right)
  then true
  else
    if charactersEqualAt left (suc right) chars
    then checkIndices (suc left) right chars
    else false

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto accumulator [] = accumulator
reverseOnto accumulator (x ∷ xs) =
  reverseOnto (x ∷ accumulator) xs

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto [] xs

listCharEqual : List Char → List Char → Bool
listCharEqual [] [] = true
listCharEqual [] (_ ∷ _) = false
listCharEqual (_ ∷ _) [] = false
listCharEqual (x ∷ xs) (y ∷ ys) =
  primCharEquality x y && listCharEqual xs ys

isPalindrome-precond : String → Set
isPalindrome-precond s = Top

isPalindrome :
  (s : String) →
  isPalindrome-precond s →
  Bool
isPalindrome s h-precond =
  let chars = primStringToList s
      length = listLength chars
  in
    if natLessOrEqual length one
    then true
    else
      let approach1 = checkIndices zero (predecessor length) chars
          reversed = reverseList chars
          approach2 = listCharEqual chars reversed
      in approach1 && approach2

isPalindrome-postcond :
  (s : String) →
  (result : Bool) →
  isPalindrome-precond s →
  Set
isPalindrome-postcond s result h-precond =
  let chars = primStringToList s
  in
    ((result ≡ true) → chars ≡ reverseList chars) ∧
    ((result ≡ false) →
      Not (chars ≡ []) ∧ Not (chars ≡ reverseList chars))

isPalindrome-spec-satisfied : Set
isPalindrome-spec-satisfied =
  (s : String) →
  (h-precond : isPalindrome-precond s) →
  isPalindrome-postcond
    s
    (isPalindrome s h-precond)
    h-precond
