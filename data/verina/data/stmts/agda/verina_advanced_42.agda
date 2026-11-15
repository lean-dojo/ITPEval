-- Statement-only formalization of VERINA corpus artifact verina_advanced_42,
-- catalog title "maxProfit": a deterministic list program computes the greatest
-- profit from buying at an earlier stock price and selling at a later one, and
-- is connected to its full correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced42 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 2 _∨_ _↔_
infixr 3 _∧_
infixr 5 _&&_ _||_
infix 4 _≤_ _<_

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

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natGreaterOrEqual : Nat → Nat → Bool
natGreaterOrEqual m n = natLessOrEqual n m

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natSub : Nat → Nat → Nat
natSub n zero = n
natSub zero (suc _) = zero
natSub (suc m) (suc n) = natSub m n

natMin : Nat → Nat → Nat
natMin m n =
  if natLessOrEqual m n
  then m
  else n

natMax : Nat → Nat → Nat
natMax m n =
  if natLessOrEqual m n
  then n
  else m

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) = predicate x ∧ All predicate xs

Pairwise :
  {A : Set} →
  (A → A → Set) →
  List A →
  Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x
  then true
  else anyList predicate xs

record NatPair : Set where
  constructor pair
  field
    pairFirst : Nat
    pairSecond : Nat

maxProfit-precond : List Nat → Set
maxProfit-precond prices = Top

updateMinAndProfit :
  Nat →
  Nat →
  Nat →
  NatPair
updateMinAndProfit price minSoFar currentMaxProfit =
  let newMin = natMin minSoFar price
      profit =
        if natLess minSoFar price
        then natSub price minSoFar
        else zero
      newMaxProfit = natMax currentMaxProfit profit
  in pair newMin newMaxProfit

maxProfitAux : List Nat → Nat → Nat → Nat
maxProfitAux [] minSoFar currentMaxProfit = currentMaxProfit
maxProfitAux (price ∷ prices) minSoFar currentMaxProfit
  with updateMinAndProfit price minSoFar currentMaxProfit
... | pair newMin newMaxProfit =
  maxProfitAux prices newMin newMaxProfit

maxProfit :
  (prices : List Nat) →
  maxProfit-precond prices →
  Nat
maxProfit [] h-precond = zero
maxProfit (price ∷ prices) h-precond =
  maxProfitAux prices price zero

record IndexedNat : Set where
  constructor indexed
  field
    indexedValue : Nat
    indexedPosition : Nat

open IndexedNat public

zipIdxFrom : Nat → List Nat → List IndexedNat
zipIdxFrom position [] = []
zipIdxFrom position (value ∷ values) =
  indexed value position ∷ zipIdxFrom (suc position) values

zipIdx : List Nat → List IndexedNat
zipIdx values = zipIdxFrom zero values

profitBound :
  Nat →
  IndexedNat →
  IndexedNat →
  Set
profitBound result earlier later =
  indexedPosition earlier < indexedPosition later →
  natSub (indexedValue later) (indexedValue earlier) ≤ result

noProfitableTransaction : List IndexedNat → Bool
noProfitableTransaction entries =
  allList
    (λ earlier →
      allList
        (λ later →
          natGreaterOrEqual
            (indexedPosition earlier)
            (indexedPosition later)
          ||
          natLessOrEqual
            (indexedValue later)
            (indexedValue earlier))
        entries)
    entries

achievesProfit : Nat → IndexedNat → IndexedNat → Bool
achievesProfit result earlier later =
  natLess
    (indexedPosition earlier)
    (indexedPosition later)
  &&
  natEqual
    (natSub (indexedValue later) (indexedValue earlier))
    result

someTransactionAchieves : Nat → List IndexedNat → Bool
someTransactionAchieves result entries =
  anyList
    (λ earlier →
      anyList
        (λ later → achievesProfit result earlier later)
        entries)
    entries

one : Nat
one = suc zero

maxProfit-postcond :
  (prices : List Nat) →
  (result : Nat) →
  maxProfit-precond prices →
  Set
maxProfit-postcond prices result h-precond =
  let entries = zipIdx prices
  in
    Pairwise (profitBound result) entries
    ∧
    ((result ≡ zero)
      ↔
      ((listLength prices ≤ one)
        ∨ IsTrue (noProfitableTransaction entries)))
    ∧
    (zero < result →
      IsTrue (someTransactionAchieves result entries))

maxProfit-spec-satisfied : Set
maxProfit-spec-satisfied =
  (prices : List Nat) →
  (h-precond : maxProfit-precond prices) →
  maxProfit-postcond
    prices
    (maxProfit prices h-precond)
    h-precond
