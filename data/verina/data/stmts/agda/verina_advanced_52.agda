-- Statement-only formalization of VERINA corpus artifact verina_advanced_52,
-- catalog title "minOperations": a deterministic reverse-list scan counts the
-- minimum removals needed to collect every natural number from 1 through k,
-- under the stated coverage precondition. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced52 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

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

chooseSet : Bool → Set → Set → Set
chooseSet true when-true when-false = when-true
chooseSet false when-true when-false = when-false

boolAnd : Bool → Bool → Bool
boolAnd true right = right
boolAnd false right = false

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

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

memberNat : Nat → List Nat → Bool
memberNat sought [] = false
memberNat sought (x ∷ xs) =
  if natEqual sought x
  then true
  else memberNat sought xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

targetNumbers : Nat → List Nat
targetNumbers k = rangeFrom (suc zero) k

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto [] accumulator = accumulator
reverseOnto (x ∷ xs) accumulator =
  reverseOnto xs (x ∷ accumulator)

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto xs []

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) = x ∷ takeList n xs

predNat : Nat → Nat
predNat zero = zero
predNat (suc n) = n

minOperations-precond : List Nat → Nat → Set
minOperations-precond nums k =
  IsTrue
    (allList
      (λ n → memberNat n nums)
      (targetNumbers k))

minOperations-loop :
  List Nat →
  List Nat →
  Nat →
  Nat →
  Nat →
  Nat
minOperations-loop [] collected collected-count ops k = ops
minOperations-loop
  (head ∷ tail)
  collected
  collected-count
  ops
  k =
    let ops′ = suc ops
        relevant-and-new =
          boolAnd
            (natLess zero head)
            (boolAnd
              (natLessOrEqual head k)
              (boolNot (memberNat head collected)))
    in
      if relevant-and-new
      then
        (let collected′ = head ∷ collected
             collected-count′ = suc collected-count
         in
           if natEqual collected-count′ k
           then ops′
           else
             minOperations-loop
               tail
               collected′
               collected-count′
               ops′
               k)
      else
        minOperations-loop
          tail
          collected
          collected-count
          ops′
          k

minOperations :
  (nums : List Nat) →
  (k : Nat) →
  minOperations-precond nums k →
  Nat
minOperations nums k h-precond =
  if natEqual k zero
  then zero
  else
    minOperations-loop
      (reverseList nums)
      []
      zero
      zero
      k

minOperations-postcond :
  (nums : List Nat) →
  (k result : Nat) →
  minOperations-precond nums k →
  Set
minOperations-postcond nums k result h-precond =
  let reversed = reverseList nums
      targets = targetNumbers k
      processed = takeList result reversed
      collected-all =
        IsTrue
          (allList
            (λ n → memberNat n processed)
            targets)
      is-minimal =
        chooseSet
          (natLess zero result)
          (Not
            (IsTrue
              (allList
                (λ n →
                  memberNat
                    n
                    (takeList (predNat result) reversed))
                targets)))
          (IsTrue (natEqual k zero))
  in
    collected-all ∧ is-minimal

minOperations-spec-satisfied : Set
minOperations-spec-satisfied =
  (nums : List Nat) →
  (k : Nat) →
  (h-precond : minOperations-precond nums k) →
  minOperations-postcond
    nums
    k
    (minOperations nums k h-precond)
    h-precond
