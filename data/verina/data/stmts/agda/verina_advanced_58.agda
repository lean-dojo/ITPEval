-- Statement-only formalization of VERINA corpus artifact verina_advanced_58,
-- catalog title "nthUglyNumber": a deterministic three-index sequence program
-- returns the nth ugly number and is connected to its ugly-factor and rank
-- contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced58 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infixr 3 _∧_

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

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

five : Nat
five = suc (suc three)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

natMin : Nat → Nat → Nat
natMin m n =
  if natLessOrEqual m n
  then m
  else n

nthUglyNumber-precond : Nat → Set
nthUglyNumber-precond n = IsTrue (natLess zero n)

record NextUglyResult : Set where
  constructor next-result
  field
    nextValue : Nat
    nextC2 : Nat
    nextC3 : Nat
    nextC5 : Nat

open NextUglyResult

nextUgly :
  List Nat →
  Nat →
  Nat →
  Nat →
  NextUglyResult
nextUgly sequence c2 c3 c5 =
  let i2 = nthDefault zero c2 sequence * two
      i3 = nthDefault zero c3 sequence * three
      i5 = nthDefault zero c5 sequence * five
      next = natMin i2 (natMin i3 i5)
      c2′ =
        if natEqual next i2
        then c2 + one
        else c2
      c3′ =
        if natEqual next i3
        then c3 + one
        else c3
      c5′ =
        if natEqual next i5
        then c5 + one
        else c5
  in next-result next c2′ c3′ c5′

nthUglyLoop :
  Nat →
  List Nat →
  Nat →
  Nat →
  Nat →
  List Nat
nthUglyLoop zero sequence c2 c3 c5 = sequence
nthUglyLoop (suc remaining) sequence c2 c3 c5 =
  let step = nextUgly sequence c2 c3 c5
  in
    nthUglyLoop
      remaining
      (appendList sequence (nextValue step ∷ []))
      (nextC2 step)
      (nextC3 step)
      (nextC5 step)

nthUglyNumber :
  (n : Nat) →
  nthUglyNumber-precond n →
  Nat
nthUglyNumber n h-precond =
  let index = natSubtract n one
      sequence =
        nthUglyLoop
          index
          (one ∷ [])
          zero
          zero
          zero
  in nthDefault zero index sequence

divideOutWithFuel : Nat → Nat → Nat → Nat
divideOutWithFuel zero n p = n
divideOutWithFuel (suc fuel) n p =
  if natLess one p
  then
    if natLess zero n
    then
      if natEqual (naturalMod n p) zero
      then divideOutWithFuel fuel (naturalDiv n p) p
      else n
    else n
  else n

divideOut : Nat → Nat → Nat
divideOut n p = divideOutWithFuel n n p

isUgly : Nat → Bool
isUgly x =
  if natEqual x zero
  then false
  else
    let n1 = divideOut x two
        n2 = divideOut n1 three
        n3 = divideOut n2 five
    in natEqual n3 one

nthUglyNumber-postcond :
  (n : Nat) →
  (result : Nat) →
  nthUglyNumber-precond n →
  Set
nthUglyNumber-postcond n result h-precond =
  (isUgly result ≡ true) ∧
  (listLength (filterList isUgly (range result)) ≡
   natSubtract n one)

nthUglyNumber-spec-satisfied : Set
nthUglyNumber-spec-satisfied =
  (n : Nat) →
  (h-precond : nthUglyNumber-precond n) →
  nthUglyNumber-postcond
    n
    (nthUglyNumber n h-precond)
    h-precond
