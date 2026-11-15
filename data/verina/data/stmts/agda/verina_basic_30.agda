-- Statement-only formalization of VERINA corpus artifact verina_basic_30,
-- catalog title "elementWiseModulo": a deterministic integer-array program
-- computes Lean's Euclidean remainder at each corresponding position of two
-- equal-length nonempty arrays with nonzero divisors and is connected to its
-- size-and-indexed-value correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic30 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

zeroInt : Int
zeroInt = pos zero

moduloMagnitude : Int → Nat → Int
moduloMagnitude numerator zero = numerator
moduloMagnitude (pos n) (suc denominator) =
  pos (naturalMod n (suc denominator))
moduloMagnitude (negsuc n) (suc denominator)
  with naturalMod (suc n) (suc denominator)
... | zero = zeroInt
... | suc remainder =
  pos (natSubtract (suc denominator) (suc remainder))

integerModulo : Int → Int → Int
integerModulo numerator (pos denominator) =
  moduloMagnitude numerator denominator
integerModulo numerator (negsuc denominator) =
  moduloMagnitude numerator (suc denominator)

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

mapIndexedFrom :
  {A B : Set} →
  Nat →
  (Nat → A → B) →
  Array A →
  Array B
mapIndexedFrom index function [] = []
mapIndexedFrom index function (x ∷ xs) =
  function index x ∷
  mapIndexedFrom (suc index) function xs

elementWiseModulo-precond : Array Int → Array Int → Set
elementWiseModulo-precond a b =
  (arraySize a ≡ arraySize b) ∧
  (zero < arraySize a) ∧
  ((i : Nat) →
    i < arraySize b →
    Not (indexDefault zeroInt b i ≡ zeroInt))

elementWiseModulo :
  (a : Array Int) →
  (b : Array Int) →
  elementWiseModulo-precond a b →
  Array Int
elementWiseModulo a b h-precond =
  mapIndexedFrom
    zero
    (λ i x → integerModulo x (indexDefault zeroInt b i))
    a

elementWiseModulo-postcond :
  (a : Array Int) →
  (b : Array Int) →
  (result : Array Int) →
  elementWiseModulo-precond a b →
  Set
elementWiseModulo-postcond a b result h-precond =
  (arraySize result ≡ arraySize a) ∧
  ((i : Nat) →
    i < arraySize result →
    indexDefault zeroInt result i ≡
      integerModulo
        (indexDefault zeroInt a i)
        (indexDefault zeroInt b i))

elementWiseModulo-spec-satisfied : Set
elementWiseModulo-spec-satisfied =
  (a : Array Int) →
  (b : Array Int) →
  (h-precond : elementWiseModulo-precond a b) →
  elementWiseModulo-postcond
    a
    b
    (elementWiseModulo a b h-precond)
    h-precond
