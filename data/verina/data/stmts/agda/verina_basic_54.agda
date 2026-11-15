-- Statement-only formalization of VERINA corpus artifact verina_basic_54,
-- catalog title "CanyonSearch": a deterministic two-pointer scan of two
-- nonempty nondecreasing integer arrays returns their minimum attained
-- absolute pairwise difference. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic54 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

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

boolAnd : Bool → Bool → Bool
boolAnd true right = right
boolAnd false right = false

natAdd : Nat → Nat → Nat
natAdd zero n = n
natAdd (suc m) n = suc (natAdd m n)

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

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

natMinimum : Nat → Nat → Nat
natMinimum m n =
  if natLess m n then m else n

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

intNatAbs : Int → Nat
intNatAbs (pos n) = n
intNatAbs (negsuc n) = suc n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) =
  natLessOrEqual n m

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} →
  (A → A → Set) →
  List A →
  Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x
  then true
  else anyList predicate xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

zeroInt : Int
zeroInt = pos zero

CanyonSearch-precond : Array Int → Array Int → Set
CanyonSearch-precond a b =
  (zero < arraySize a) ∧
  (zero < arraySize b) ∧
  Pairwise IntLessOrEqual a ∧
  Pairwise IntLessOrEqual b

canyonSearchAuxWithFuel :
  Nat →
  Array Int →
  Array Int →
  Nat →
  Nat →
  Nat →
  Nat
canyonSearchAuxWithFuel zero a b m n d = d
canyonSearchAuxWithFuel (suc fuel) a b m n d =
  if boolAnd
       (natLess m (arraySize a))
       (natLess n (arraySize b))
  then
    (let ai = indexDefault zeroInt a m
         bi = indexDefault zeroInt b n
         diff = intNatAbs (intSubtract ai bi)
         new-d = natMinimum diff d
     in
       if intLessOrEqual ai bi
       then canyonSearchAuxWithFuel fuel a b (suc m) n new-d
       else canyonSearchAuxWithFuel fuel a b m (suc n) new-d)
  else d

canyonSearchAux :
  Array Int →
  Array Int →
  Nat →
  Nat →
  Nat →
  Nat
canyonSearchAux a b m n d =
  canyonSearchAuxWithFuel
    (natSubtract
      (natSubtract
        (natAdd (arraySize a) (arraySize b))
        m)
      n)
    a
    b
    m
    n
    d

CanyonSearch :
  (a : Array Int) →
  (b : Array Int) →
  CanyonSearch-precond a b →
  Nat
CanyonSearch a b h-precond =
  let first-a = indexDefault zeroInt a zero
      first-b = indexDefault zeroInt b zero
      initial-difference =
        if intLess first-a first-b
        then intNatAbs (intSubtract first-b first-a)
        else intNatAbs (intSubtract first-a first-b)
  in canyonSearchAux a b zero zero initial-difference

CanyonSearch-postcond :
  (a : Array Int) →
  (b : Array Int) →
  (result : Nat) →
  CanyonSearch-precond a b →
  Set
CanyonSearch-postcond a b result h-precond =
  IsTrue
    (anyList
      (λ ai →
        anyList
          (λ bi →
            natEqual
              result
              (intNatAbs (intSubtract ai bi)))
          b)
      a) ∧
  IsTrue
    (allList
      (λ ai →
        allList
          (λ bi →
            natLessOrEqual
              result
              (intNatAbs (intSubtract ai bi)))
          b)
      a)

CanyonSearch-spec-satisfied : Set
CanyonSearch-spec-satisfied =
  (a : Array Int) →
  (b : Array Int) →
  (h-precond : CanyonSearch-precond a b) →
  CanyonSearch-postcond
    a
    b
    (CanyonSearch a b h-precond)
    h-precond
