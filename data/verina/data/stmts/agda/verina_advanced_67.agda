-- Statement-only formalization of VERINA corpus artifact verina_advanced_67,
-- catalog title "runLengthEncode": a deterministic accumulator-based program
-- groups consecutive equal string characters into positive-length runs, with
-- adjacent runs distinct and decoding equal to the input. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced67 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primCharEquality)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using
  (String; primStringAppend; primStringFromList; primStringToList)

infixr 3 _∧_

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

record CharNatPair : Set where
  constructor pair
  field
    pairChar : Char
    pairCount : Nat

open CharNatPair public

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

reverseOnto :
  {A : Set} →
  List A →
  List A →
  List A
reverseOnto [] accumulator = accumulator
reverseOnto (x ∷ xs) accumulator =
  reverseOnto xs (x ∷ accumulator)

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto xs []

encodeAux :
  List CharNatPair →
  List Char →
  List CharNatPair
encodeAux accumulator [] =
  reverseList accumulator
encodeAux [] (current ∷ rest) =
  encodeAux (pair current (suc zero) ∷ []) rest
encodeAux
  (pair previous count ∷ accumulator-tail)
  (current ∷ rest) =
  if primCharEquality previous current
  then
    encodeAux
      (pair previous (suc count) ∷ accumulator-tail)
      rest
  else
    encodeAux
      (pair current (suc zero) ∷
       pair previous count ∷
       accumulator-tail)
      rest

runLengthEncode-precond : String → Set
runLengthEncode-precond s = Top

runLengthEncode :
  (s : String) →
  runLengthEncode-precond s →
  List CharNatPair
runLengthEncode s h-precond =
  encodeAux [] (primStringToList s)

repeatChar : Nat → Char → List Char
repeatChar zero character = []
repeatChar (suc count) character =
  character ∷ repeatChar count character

decodeRLE : List CharNatPair → String
decodeRLE [] =
  primStringFromList []
decodeRLE (pair character count ∷ tail) =
  primStringAppend
    (primStringFromList (repeatChar count character))
    (decodeRLE tail)

Positive : Nat → Set
Positive zero = Empty
Positive (suc count) = Top

AllRunsPositive : List CharNatPair → Set
AllRunsPositive [] = Top
AllRunsPositive (run ∷ runs) =
  Positive (pairCount run) ∧ AllRunsPositive runs

AdjacentRunsDistinct : List CharNatPair → Set
AdjacentRunsDistinct [] = Top
AdjacentRunsDistinct (run ∷ []) = Top
AdjacentRunsDistinct (first-run ∷ second-run ∷ runs) =
  Not (pairChar first-run ≡ pairChar second-run) ∧
  AdjacentRunsDistinct (second-run ∷ runs)

runLengthEncode-postcond :
  (s : String) →
  (result : List CharNatPair) →
  runLengthEncode-precond s →
  Set
runLengthEncode-postcond s result h-precond =
  AllRunsPositive result ∧
  AdjacentRunsDistinct result ∧
  (decodeRLE result ≡ s)

runLengthEncode-spec-satisfied : Set
runLengthEncode-spec-satisfied =
  (s : String) →
  (h-precond : runLengthEncode-precond s) →
  runLengthEncode-postcond
    s
    (runLengthEncode s h-precond)
    h-precond
