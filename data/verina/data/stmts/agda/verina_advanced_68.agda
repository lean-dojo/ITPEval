-- Statement-only formalization of VERINA corpus artifact verina_advanced_68,
-- catalog title "runLengthEncoder": a deterministic run-length encoder for
-- digit-free strings, together with its format, decoding, and emptiness
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced68 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using
  (Char; primCharEquality; primCharToNat; primNatToChar)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)
open import Agda.Builtin.String using
  (String; primStringAppend; primStringFromList; primStringToList)

infixr 5 _&&_
infixr 5 _++_

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

boolEqual : Bool → Bool → Bool
boolEqual true true = true
boolEqual true false = false
boolEqual false true = false
boolEqual false false = true

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc n) = true
natLess (suc m) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero n = true
natLessOrEqual (suc m) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto [] accumulator = accumulator
reverseOnto (x ∷ xs) accumulator =
  reverseOnto xs (x ∷ accumulator)

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto xs []

isDigit : Char → Bool
isDigit c =
  natLessOrEqual 48 (primCharToNat c) &&
  natLessOrEqual (primCharToNat c) 57

allNotDigit : List Char → Bool
allNotDigit [] = true
allNotDigit (c ∷ cs) =
  boolNot (isDigit c) && allNotDigit cs

runLengthEncoder-precond : String → Set
runLengthEncoder-precond input =
  IsTrue (allNotDigit (primStringToList input))

ten : Nat
ten = 10

digitsWithFuel : Nat → Nat → List Char
digitsWithFuel zero n = []
digitsWithFuel (suc fuel) n =
  if natLess n ten
  then primNatToChar (n + 48) ∷ []
  else
    digitsWithFuel fuel (naturalDiv n ten) ++
    (primNatToChar (naturalMod n ten + 48) ∷ [])

numToString : Nat → String
numToString n =
  primStringFromList (digitsWithFuel (suc n) n)

emptyString : String
emptyString = primStringFromList []

singletonString : Char → String
singletonString c = primStringFromList (c ∷ [])

encode :
  List Char →
  Maybe Char →
  Nat →
  String
encode [] nothing count = emptyString
encode [] (just current) count =
  primStringAppend
    (singletonString current)
    (numToString count)
encode (c ∷ rest) nothing count =
  encode rest (just c) 1
encode (c ∷ rest) (just current) count =
  if primCharEquality c current
  then encode rest (just current) (count + 1)
  else
    primStringAppend
      (primStringAppend
        (singletonString current)
        (numToString count))
      (encode rest (just c) 1)

runLengthEncoder :
  (input : String) →
  runLengthEncoder-precond input →
  String
runLengthEncoder input h-precond with primStringToList input
... | [] = emptyString
... | first ∷ rest = encode rest (just first) 1

record CharNatPair : Set where
  constructor pair
  field
    pairChar : Char
    pairCount : Nat

updateCount : Maybe Nat → Nat → Nat
updateCount nothing digit = digit
updateCount (just count) digit = count * ten + digit

mutual
  parseState :
    List Char →
    Maybe Char →
    Maybe Nat →
    List CharNatPair →
    List CharNatPair
  parseState [] nothing currentCount accumulator =
    accumulator
  parseState [] (just current) nothing accumulator =
    accumulator
  parseState [] (just current) (just count) accumulator =
    pair current count ∷ accumulator
  parseState (c ∷ cs) currentChar currentCount accumulator =
    if isDigit c
    then parseDigit cs c currentChar currentCount accumulator
    else parseNonDigit cs c currentChar currentCount accumulator

  parseDigit :
    List Char →
    Char →
    Maybe Char →
    Maybe Nat →
    List CharNatPair →
    List CharNatPair
  parseDigit cs c nothing currentCount accumulator =
    []
  parseDigit cs c (just current) currentCount accumulator =
    parseState
      cs
      (just current)
      (just
        (updateCount
          currentCount
          (natSubtract (primCharToNat c) 48)))
      accumulator

  parseNonDigit :
    List Char →
    Char →
    Maybe Char →
    Maybe Nat →
    List CharNatPair →
    List CharNatPair
  parseNonDigit cs c nothing currentCount accumulator =
    parseState cs (just c) nothing accumulator
  parseNonDigit cs c (just current) nothing accumulator =
    parseState cs (just c) nothing accumulator
  parseNonDigit cs c (just current) (just count) accumulator =
    parseState
      cs
      (just c)
      nothing
      (pair current count ∷ accumulator)

parseEncodedString : String → List CharNatPair
parseEncodedString result =
  reverseList
    (parseState
      (primStringToList result)
      nothing
      nothing
      [])

mutual
  checkPairs : List Char → Bool → Bool
  checkPairs [] nowDigit = true
  checkPairs (c ∷ cs) nowDigit =
    if nowDigit && isDigit c
    then checkPairs cs true
    else checkFollowingDigit cs

  checkFollowingDigit : List Char → Bool
  checkFollowingDigit [] = false
  checkFollowingDigit (d ∷ ds) =
    if isDigit d
    then checkPairs ds true
    else false

formatValid : String → Bool
formatValid result =
  checkPairs (primStringToList result) false

replicateChar : Nat → Char → List Char
replicateChar zero c = []
replicateChar (suc count) c =
  c ∷ replicateChar count c

expandPairs : List CharNatPair → List Char
expandPairs [] = []
expandPairs (pair c count ∷ pairs) =
  replicateChar count c ++ expandPairs pairs

charListEqual : List Char → List Char → Bool
charListEqual [] [] = true
charListEqual [] (_ ∷ _) = false
charListEqual (_ ∷ _) [] = false
charListEqual (x ∷ xs) (y ∷ ys) =
  primCharEquality x y && charListEqual xs ys

contentValid : String → String → Bool
contentValid input result =
  charListEqual
    (expandPairs (parseEncodedString result))
    (primStringToList input)

isEmptyChars : List Char → Bool
isEmptyChars [] = true
isEmptyChars (_ ∷ _) = false

nonEmptyValid : String → String → Bool
nonEmptyValid input result =
  boolEqual
    (isEmptyChars (primStringToList input))
    (isEmptyChars (primStringToList result))

runLengthEncoder-postcond :
  (input : String) →
  (result : String) →
  runLengthEncoder-precond input →
  Set
runLengthEncoder-postcond input result h-precond =
  IsTrue
    (formatValid result &&
     contentValid input result &&
     nonEmptyValid input result)

runLengthEncoder-spec-satisfied : Set
runLengthEncoder-spec-satisfied =
  (input : String) →
  (h-precond : runLengthEncoder-precond input) →
  runLengthEncoder-postcond
    input
    (runLengthEncoder input h-precond)
    h-precond
