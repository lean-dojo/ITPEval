-- Statement-only formalization of VERINA corpus artifact verina_basic_73,
-- catalog title "Match": a deterministic string scan matches equal-length
-- strings pointwise, allowing '?' in the pattern as a wildcard, and is
-- connected to its Boolean correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic73 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using
  (Char; primCharEquality; primNatToChar)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String; primStringToList)

infixr 2 _∨_
infix 3 _↔_
infix 4 _≤_ _<_

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

nullChar : Char
nullChar = primNatToChar zero

Match-precond : String → String → Set
Match-precond s p =
  listLength (primStringToList s) ≡
  listLength (primStringToList p)

-- This structural scan is the source loop with the common index removed.
-- An exhausted pattern uses Char's default null value, as Lean's get! does.
Match-loop : List Char → List Char → Bool
Match-loop [] p-chars = true
Match-loop (s-char ∷ s-chars) [] =
  if primCharEquality s-char nullChar
  then Match-loop s-chars []
  else false
Match-loop (s-char ∷ s-chars) (p-char ∷ p-chars) =
  if primCharEquality s-char p-char
  then Match-loop s-chars p-chars
  else
    if primCharEquality p-char '?'
    then Match-loop s-chars p-chars
    else false

Match :
  (s : String) →
  (p : String) →
  Match-precond s p →
  Bool
Match s p h-precond =
  Match-loop
    (primStringToList s)
    (primStringToList p)

Match-postcond :
  (s : String) →
  (p : String) →
  (result : Bool) →
  Match-precond s p →
  Set
Match-postcond s p result h-precond =
  let s-chars = primStringToList s
      p-chars = primStringToList p
  in
    (result ≡ true) ↔
    ((n : Nat) →
      n < listLength s-chars →
      (indexDefault nullChar s-chars n ≡
        indexDefault nullChar p-chars n) ∨
      (indexDefault nullChar p-chars n ≡ '?'))

Match-spec-satisfied : Set
Match-spec-satisfied =
  (s : String) →
  (p : String) →
  (h-precond : Match-precond s p) →
  Match-postcond
    s
    p
    (Match s p h-precond)
    h-precond
