-- Statement-only formalization of VERINA corpus artifact verina_advanced_5,
-- catalog title "addTwoNumbers": a deterministic carry-based program adds two
-- canonical nonempty little-endian decimal digit lists and is connected to its
-- numeric-value and canonical-output contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced5 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infixr 2 _∨_
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

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

ten : Nat
ten =
  suc
    (suc
      (suc
        (suc
          (suc
            (suc
              (suc
                (suc
                  (suc
                    (suc zero)))))))))

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

listToNat : List Nat → Nat
listToNat [] = zero
listToNat (digit ∷ digits) =
  digit + ten * listToNat digits

AllDigits : List Nat → Set
AllDigits [] = Top
AllDigits (digit ∷ digits) =
  (digit < ten) ∧ AllDigits digits

getLastDefault : {A : Set} → A → List A → A
getLastDefault default [] = default
getLastDefault default (x ∷ []) = x
getLastDefault default (x ∷ y ∷ ys) =
  getLastDefault default (y ∷ ys)

record addTwoNumbers-precond (l1 l2 : List Nat) : Set where
  constructor precondition
  field
    l1-nonempty : zero < listLength l1
    l2-nonempty : zero < listLength l2
    l1-digits : AllDigits l1
    l2-digits : AllDigits l2
    l1-canonical :
      Not (getLastDefault zero l1 ≡ zero) ∨
      (l1 ≡ zero ∷ [])
    l2-canonical :
      Not (getLastDefault zero l2 ≡ zero) ∨
      (l2 ≡ zero ∷ [])

addAux : List Nat → List Nat → Nat → List Nat
addAux [] [] carry =
  if natEqual carry zero
  then []
  else (carry ∷ [])
addAux (h1 ∷ t1) [] carry =
  let sum = h1 + carry
  in
    naturalMod sum ten ∷
    addAux t1 [] (naturalDiv sum ten)
addAux [] (h2 ∷ t2) carry =
  let sum = h2 + carry
  in
    naturalMod sum ten ∷
    addAux [] t2 (naturalDiv sum ten)
addAux (h1 ∷ t1) (h2 ∷ t2) carry =
  let sum = (h1 + h2) + carry
  in
    naturalMod sum ten ∷
    addAux t1 t2 (naturalDiv sum ten)

addTwoNumbers :
  (l1 l2 : List Nat) →
  addTwoNumbers-precond l1 l2 →
  List Nat
addTwoNumbers l1 l2 h-precond =
  addAux l1 l2 zero

addTwoNumbers-postcond :
  (l1 l2 result : List Nat) →
  addTwoNumbers-precond l1 l2 →
  Set
addTwoNumbers-postcond l1 l2 result h-precond =
  (listToNat result ≡ listToNat l1 + listToNat l2) ∧
  AllDigits result ∧
  (Not (getLastDefault zero result ≡ zero) ∨
    ((l1 ≡ zero ∷ []) ∧
      (l2 ≡ zero ∷ []) ∧
      (result ≡ zero ∷ [])))

addTwoNumbers-spec-satisfied : Set
addTwoNumbers-spec-satisfied =
  (l1 l2 : List Nat) →
  (h-precond : addTwoNumbers-precond l1 l2) →
  addTwoNumbers-postcond
    l1
    l2
    (addTwoNumbers l1 l2 h-precond)
    h-precond
