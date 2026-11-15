-- Statement-only formalization of VERINA corpus artifact verina_basic_80,
-- catalog title "only_once": a deterministic integer-array scan returns true
-- exactly when the key occurs once and is connected to its occurrence-count
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic80 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

record Top : Set where
  constructor top

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

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

one : Nat
one = suc zero

Array : Set → Set
Array A = List A

dropArray : {A : Set} → Nat → Array A → Array A
dropArray zero xs = xs
dropArray (suc n) [] = []
dropArray (suc n) (_ ∷ xs) = dropArray n xs

foldl :
  {A B : Set} →
  (A → B → A) →
  A →
  List B →
  A
foldl step accumulator [] = accumulator
foldl step accumulator (x ∷ xs) =
  foldl step (step accumulator x) xs

only-once-precond : Array Int → Int → Set
only-once-precond a key = Top

scan-only-once :
  {A : Set} →
  (A → A → Bool) →
  A →
  Array A →
  Nat →
  Bool
scan-only-once equal key [] keyCount =
  natEqual keyCount one
scan-only-once equal key (value ∷ rest) keyCount =
  let newCount =
        if equal value key
        then suc keyCount
        else keyCount
  in scan-only-once equal key rest newCount

-- Dropping i elements exposes exactly the suffix traversed by the source
-- index loop from i; the accumulator and final equality test are unchanged.
only-once-loop :
  {A : Set} →
  (A → A → Bool) →
  Array A →
  A →
  Nat →
  Nat →
  Bool
only-once-loop equal a key i keyCount =
  scan-only-once equal key (dropArray i a) keyCount

only-once :
  (a : Array Int) →
  (key : Int) →
  only-once-precond a key →
  Bool
only-once a key h-precond =
  only-once-loop intEqual a key zero zero

count-step :
  {A : Set} →
  (A → A → Bool) →
  A →
  Nat →
  A →
  Nat
count-step equal key accumulator value =
  if equal value key
  then suc accumulator
  else accumulator

count-occurrences :
  {A : Set} →
  (A → A → Bool) →
  Array A →
  A →
  Nat
count-occurrences equal a key =
  foldl (count-step equal key) zero a

only-once-postcond :
  (a : Array Int) →
  (key : Int) →
  (result : Bool) →
  only-once-precond a key →
  Set
only-once-postcond a key result h-precond =
  ((count-occurrences intEqual a key ≡ one) →
    IsTrue result) ∧
  (Not (count-occurrences intEqual a key ≡ one) →
    Not (IsTrue result))

only-once-spec-satisfied : Set
only-once-spec-satisfied =
  (a : Array Int) →
  (key : Int) →
  (h-precond : only-once-precond a key) →
  only-once-postcond
    a
    key
    (only-once a key h-precond)
    h-precond
