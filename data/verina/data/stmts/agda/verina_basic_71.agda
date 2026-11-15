-- Statement-only formalization of VERINA corpus artifact verina_basic_71,
-- catalog title "LongestCommonPrefix": a deterministic indexed recursion
-- computes the longest common prefix of two character lists and is connected
-- to its complete prefix-and-maximality correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic71 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primCharEquality)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 2 _∨_
infixr 3 _∧_
infix 4 _≤_

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

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natMin : Nat → Nat → Nat
natMin zero n = zero
natMin (suc m) zero = zero
natMin (suc m) (suc n) = suc (natMin m n)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) = x ∷ takeList n xs

listIndex : {A : Set} → Nat → List A → Maybe A
listIndex zero [] = nothing
listIndex zero (x ∷ xs) = just x
listIndex (suc n) [] = nothing
listIndex (suc n) (_ ∷ xs) = listIndex n xs

LongestCommonPrefix-precond : List Char → List Char → Set
LongestCommonPrefix-precond str1 str2 = Top

LongestCommonPrefix-aux :
  Nat →
  List Char →
  List Char →
  Nat →
  Nat →
  List Char →
  List Char
LongestCommonPrefix-aux zero str1 str2 minLength idx acc = acc
LongestCommonPrefix-aux
  (suc fuel) str1 str2 minLength idx acc
  with natLess idx minLength
... | false = acc
... | true with listIndex idx str1 | listIndex idx str2
...   | just c1 | just c2 =
  if primCharEquality c1 c2
  then
    LongestCommonPrefix-aux
      fuel
      str1
      str2
      minLength
      (suc idx)
      (appendList acc (c1 ∷ []))
  else acc
...   | _ | _ = acc

LongestCommonPrefix :
  (str1 : List Char) →
  (str2 : List Char) →
  LongestCommonPrefix-precond str1 str2 →
  List Char
LongestCommonPrefix str1 str2 h-precond =
  let minLength = natMin (listLength str1) (listLength str2)
  in
    LongestCommonPrefix-aux
      minLength
      str1
      str2
      minLength
      zero
      []

LongestCommonPrefix-postcond :
  (str1 : List Char) →
  (str2 : List Char) →
  (result : List Char) →
  LongestCommonPrefix-precond str1 str2 →
  Set
LongestCommonPrefix-postcond str1 str2 result h-precond =
  (listLength result ≤ listLength str1) ∧
  (result ≡ takeList (listLength result) str1) ∧
  (listLength result ≤ listLength str2) ∧
  (result ≡ takeList (listLength result) str2) ∧
  ((listLength result ≡ listLength str1) ∨
   (listLength result ≡ listLength str2) ∨
   Not
     (listIndex (listLength result) str1 ≡
      listIndex (listLength result) str2))

LongestCommonPrefix-spec-satisfied : Set
LongestCommonPrefix-spec-satisfied =
  (str1 : List Char) →
  (str2 : List Char) →
  (h-precond : LongestCommonPrefix-precond str1 str2) →
  LongestCommonPrefix-postcond
    str1
    str2
    (LongestCommonPrefix str1 str2 h-precond)
    h-precond
