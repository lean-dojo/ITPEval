-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_lexicographic_permutations_1_Top_to_seqqtvc: the
-- loop verification condition for converting an integer array to a sequence
-- by appending its entries while preserving length and indexed values.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021LexicographicPermutations1TopToSeqVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 5 _++_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthNat : List Int → Nat → Int
nthNat xs index = nthDefault zeroZ index xs

nthInt : List Int → Int → Int
nthInt xs index = nthNat xs (toNat index)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

InitialState : List Int → Set
InitialState a =
  lengthZ ([] {A = Int}) ≡ zeroZ
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z zeroZ) →
    nthInt [] i ≡ nthInt a i)

LoopInvariant : List Int → Int → List Int → Set
LoopInvariant a o1 s =
  (zeroZ ≤Z lengthZ s ∧ lengthZ s ≤Z o1)
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z lengthZ s) →
    nthInt s i ≡ nthInt a i)

AppendStep : List Int → List Int → Set
AppendStep a s =
  let
    o2 = nthNat a (length s)
    o3 = s ++ (o2 ∷ [])
  in
  (lengthZ o3 ≡ addInt oneZ (lengthZ s)
   ∧ nthNat o3 (length s) ≡ o2
   ∧
   ((i : Int) →
     (zeroZ ≤Z i ∧ i <Z lengthZ s) →
     nthInt o3 i ≡ nthInt s i))
  →
  (lengthZ o3 ≡ addInt (lengthZ s) oneZ
   ∧
   ((i : Int) →
     (zeroZ ≤Z i ∧
      i <Z addInt (lengthZ s) oneZ) →
     nthInt o3 i ≡ nthInt a i))

ExitStep : List Int → Int → List Int → Set
ExitStep a o1 s =
  (lengthZ s ≡ addInt o1 oneZ
   ∧
   ((i : Int) →
     (zeroZ ≤Z i ∧ i <Z addInt o1 oneZ) →
     nthInt s i ≡ nthInt a i))
  →
  (length s ≡ length a
   ∧
   ((i : Int) →
     (zeroZ ≤Z i ∧ i <Z lengthZ s) →
     nthInt s i ≡ nthInt a i))

LoopBody : List Int → Int → List Int → Set
LoopBody a o1 s =
  LoopInvariant a o1 s
  →
  ((zeroZ ≤Z lengthZ s ∧ lengthZ s <Z lengthZ a)
   ∧ AppendStep a s)
  ∧ ExitStep a o1 s

EmptyResult : List Int → Set
EmptyResult a =
  let r : List Int
      r = []
  in
  length r ≡ length a
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z lengthZ r) →
    nthInt r i ≡ nthInt a i)

to-seq'vc : Set
to-seq'vc =
  (a : List Int) →
  let o1 = subtractInt (lengthZ a) oneZ
  in
  (zeroZ ≤Z addInt o1 oneZ →
    InitialState a
    ∧ ((s : List Int) → LoopBody a o1 s))
  ∧
  (addInt o1 oneZ <Z zeroZ →
    EmptyResult a)
