-- Statement-only formalization of VERINA corpus artifact verina_basic_39,
-- catalog title "rotateRight": a deterministic integer-list program rotates
-- entries to the right by a natural offset using modular indices and is
-- connected to its length and pointwise correctness contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic39 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; mod-helper)

infixr 3 _∧_
infix 4 _≤_ _<_

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

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

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

intModuloByNat : Int → Nat → Int
intModuloByNat x zero = x
intModuloByNat (pos n) (suc denominator) =
  pos (naturalMod n (suc denominator))
intModuloByNat (negsuc n) (suc denominator) =
  let divisor = suc denominator
      remainder = naturalMod (suc n) divisor
  in
    if natEqual remainder zero
    then pos zero
    else pos (natSubtract divisor remainder)

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc n) = zero

zeroInt : Int
zeroInt = pos zero

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

headDefault : {A : Set} → A → List A → A
headDefault default [] = default
headDefault default (x ∷ xs) = x

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

indexMaybe : {A : Set} → List A → Nat → Maybe A
indexMaybe [] index = nothing
indexMaybe (x ∷ xs) zero = just x
indexMaybe (x ∷ xs) (suc index) = indexMaybe xs index

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

rotatedIndex : Nat → Nat → Nat → Nat
rotatedIndex i n len =
  intToNat
    (intModuloByNat
      (intAdd
        (intSubtract (pos i) (pos n))
        (pos len))
      len)

rotateRight-precond : List Int → Nat → Set
rotateRight-precond l n = Top

rotateRight :
  (l : List Int) →
  (n : Nat) →
  rotateRight-precond l n →
  List Int
rotateRight l n h-precond =
  let len = listLength l
  in
    if natEqual len zero
    then l
    else
      mapList
        (λ i →
          indexDefault
            (headDefault zeroInt l)
            l
            (rotatedIndex i n len))
        (range len)

rotateRight-postcond :
  (l : List Int) →
  (n : Nat) →
  (result : List Int) →
  rotateRight-precond l n →
  Set
rotateRight-postcond l n result h-precond =
  (listLength result ≡ listLength l) ∧
  ((i : Nat) →
    i < listLength l →
    indexMaybe result i ≡
      indexMaybe l (rotatedIndex i n (listLength l)))

rotateRight-spec-satisfied : Set
rotateRight-spec-satisfied =
  (l : List Int) →
  (n : Nat) →
  (h-precond : rotateRight-precond l n) →
  rotateRight-postcond
    l
    n
    (rotateRight l n h-precond)
    h-precond
