-- Statement-only formalization of VERINA corpus artifact verina_advanced_8,
-- catalog title "canCompleteCircuit": a deterministic gas-station program
-- returns the least feasible circuit start, or -1 when none exists, and is
-- connected to its full prefix-balance correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced8 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

infixr 3 _∧_
infix 4 _≤_ _<_

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

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual x y = boolNot (intLess y x)

intGreaterOrEqual : Int → Int → Bool
intGreaterOrEqual x y = intLessOrEqual y x

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

minusOne : Int
minusOne = negsuc zero

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

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

range : Nat → List Nat
range count = rangeFrom zero count

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

record IntPair : Set where
  constructor pair
  field
    pairFirst : Int
    pairSecond : Int

zipList : List Int → List Int → List IntPair
zipList [] ys = []
zipList xs [] = []
zipList (x ∷ xs) (y ∷ ys) =
  pair x y ∷ zipList xs ys

canCompleteCircuit-precond : List Int → List Int → Set
canCompleteCircuit-precond gas cost =
  (zero < listLength gas) ∧
  (listLength gas ≡ listLength cost)

sumList : List Int → Int
sumList values = foldLeft intAdd zeroInt values

unusedLoop :
  List Int →
  List Int →
  Nat →
  Int →
  Nat →
  Int
unusedLoop [] [] index tank start = pos start
unusedLoop [] (_ ∷ _) index tank start = minusOne
unusedLoop (_ ∷ _) [] index tank start = minusOne
unusedLoop (g ∷ gs) (c ∷ cs) index tank start =
  let new-tank = intSubtract (intAdd tank g) c
  in
    if intLess new-tank zeroInt
    then unusedLoop gs cs (suc index) zeroInt (suc index)
    else unusedLoop gs cs (suc index) new-tank start

walk :
  List IntPair →
  Nat →
  Int →
  Nat →
  Int
walk [] index tank start = pos start
walk (pair g c ∷ rest) index tank start =
  let new-tank = intSubtract (intAdd tank g) c
  in
    if intLess new-tank zeroInt
    then walk rest (suc index) zeroInt (suc index)
    else walk rest (suc index) new-tank start

canCompleteCircuit :
  (gas cost : List Int) →
  canCompleteCircuit-precond gas cost →
  Int
canCompleteCircuit gas cost h-precond =
  let total-gas = sumList gas
      total-cost = sumList cost
  in
    if intLess total-gas total-cost
    then minusOne
    else walk (zipList gas cost) zero zeroInt zero

prefixBalance :
  List Int →
  List Int →
  Nat →
  Nat →
  Int
prefixBalance gas cost start prefix-end =
  foldLeft
    (λ tank offset →
      let station =
            naturalMod
              (start + offset)
              (listLength gas)
      in
        intSubtract
          (intAdd
            tank
            (indexDefault zeroInt gas station))
          (indexDefault zeroInt cost station))
    zeroInt
    (range (suc prefix-end))

validStart :
  List Int →
  List Int →
  Nat →
  Bool
validStart gas cost start =
  allList
    (λ prefix-end →
      intGreaterOrEqual
        (prefixBalance gas cost start prefix-end)
        zeroInt)
    (range (listLength gas))

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc n) = zero

noValidStart :
  List Int →
  List Int →
  List Nat →
  Bool
noValidStart gas cost starts =
  allList
    (λ start → boolNot (validStart gas cost start))
    starts

canCompleteCircuit-postcond :
  (gas cost : List Int) →
  (result : Int) →
  canCompleteCircuit-precond gas cost →
  Set
canCompleteCircuit-postcond gas cost result h-precond =
  IsTrue (intGreaterOrEqual result minusOne) ∧
  ((result ≡ minusOne →
      IsTrue
        (noValidStart gas cost (range (listLength gas)))) ∧
   (IsTrue (intGreaterOrEqual result zeroInt) →
      IsTrue (intLess result (pos (listLength gas))) ∧
      IsTrue (validStart gas cost (intToNat result)) ∧
      IsTrue
        (noValidStart gas cost (range (intToNat result)))))

canCompleteCircuit-spec-satisfied : Set
canCompleteCircuit-spec-satisfied =
  (gas cost : List Int) →
  (h-precond : canCompleteCircuit-precond gas cost) →
  canCompleteCircuit-postcond
    gas
    cost
    (canCompleteCircuit gas cost h-precond)
    h-precond
