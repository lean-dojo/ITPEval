-- Statement-only formalization of VERINA corpus artifact verina_basic_103,
-- catalog title "UpdateElements": a deterministic integer-array program
-- increments element 4 by 3, sets element 7 to 516, and is connected to its
-- size-preserving point-update correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic103 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤_ _<_
infixr 3 _∧_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

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

zeroInt : Int
zeroInt = pos zero

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

updateAt : {A : Set} → Array A → Nat → A → Array A
updateAt [] index value = []
updateAt (x ∷ xs) zero value = value ∷ xs
updateAt (x ∷ xs) (suc index) value =
  x ∷ updateAt xs index value

UpdateElements-precond : Array Int → Set
UpdateElements-precond a = 8 ≤ arraySize a

UpdateElements :
  (a : Array Int) →
  UpdateElements-precond a →
  Array Int
UpdateElements a h-precond =
  let a1 =
        updateAt
          a
          4
          (intAdd (indexDefault zeroInt a 4) (pos 3))
      a2 = updateAt a1 7 (pos 516)
  in a2

UpdateElements-postcond :
  (a result : Array Int) →
  UpdateElements-precond a →
  Set
UpdateElements-postcond a result h-precond =
  (arraySize result ≡ arraySize a) ∧
  (indexDefault zeroInt result 4 ≡
    intAdd (indexDefault zeroInt a 4) (pos 3)) ∧
  (indexDefault zeroInt result 7 ≡ pos 516) ∧
  ((i : Nat) →
    i < arraySize a →
    Not (i ≡ 4) →
    Not (i ≡ 7) →
    indexDefault zeroInt result i ≡ indexDefault zeroInt a i)

UpdateElements-spec-satisfied : Set
UpdateElements-spec-satisfied =
  (a : Array Int) →
  (h-precond : UpdateElements-precond a) →
  UpdateElements-postcond
    a
    (UpdateElements a h-precond)
    h-precond
