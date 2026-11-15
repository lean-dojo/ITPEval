-- Statement-only formalization of VERINA corpus artifact verina_basic_21,
-- catalog title "isSublist": a deterministic bounded scan returns true
-- exactly when the first integer list occurs as a contiguous block in the
-- second list and is connected to its correctness contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic21 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 2 _↔_
infixr 3 _∧_
infix 4 _≤_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

data IsTrue : Bool → Set where
  true-witness : IsTrue true

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

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

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

listIntEqual : List Int → List Int → Bool
listIntEqual [] [] = true
listIntEqual [] (_ ∷ _) = false
listIntEqual (_ ∷ _) [] = false
listIntEqual (x ∷ xs) (y ∷ ys) =
  if intEqual x y
  then listIntEqual xs ys
  else false

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) = x ∷ takeList n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

isSublist-check :
  List Int →
  List Int →
  Nat →
  Nat →
  Nat →
  Nat →
  Bool
isSublist-check sub main subLen mainLen i zero = false
isSublist-check sub main subLen mainLen i (suc fuel) =
  if natLess mainLen (i + subLen)
  then false
  else
    if listIntEqual sub (takeList subLen (dropList i main))
    then true
    else
      if natLessOrEqual (suc i) mainLen
      then
        isSublist-check
          sub
          main
          subLen
          mainLen
          (suc i)
          fuel
      else false

isSublist-precond : List Int → List Int → Set
isSublist-precond sub main = Top

isSublist :
  (sub main : List Int) →
  isSublist-precond sub main →
  Bool
isSublist sub main h-precond =
  let subLen = listLength sub
      mainLen = listLength main
  in
    if natLess mainLen subLen
    then false
    else
      isSublist-check
        sub
        main
        subLen
        mainLen
        zero
        (suc mainLen)

isSublist-postcond :
  (sub main : List Int) →
  (result : Bool) →
  isSublist-precond sub main →
  Set
isSublist-postcond sub main result h-precond =
  (Σ Nat
    (λ i →
      ((i + listLength sub) ≤ listLength main) ∧
      (sub ≡ takeList (listLength sub) (dropList i main))))
  ↔ IsTrue result

isSublist-spec-satisfied : Set
isSublist-spec-satisfied =
  (sub main : List Int) →
  (h-precond : isSublist-precond sub main) →
  isSublist-postcond
    sub
    main
    (isSublist sub main h-precond)
    h-precond
