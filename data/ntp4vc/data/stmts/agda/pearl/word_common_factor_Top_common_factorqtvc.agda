-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/word_common_factor_Top_common_factorqtvc: the verification condition
-- showing that two commuting words are nonnegative powers of a common word.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module word_common_factor_Top_common_factorqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≢_ _≤Z_ _<N_
infixr 5 _++_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≢_ : {A : Set} → A → A → Set
x ≢ y = Not (x ≡ y)

record Inhabited (A : Set) : Set where
  constructor inhabited
  field
    witness : A

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<N_ : Nat → Nat → Set
x <N y = natLess x y ≡ true

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

record PowerModel (Char : Set) : Set where
  field
    power : List Char → Int → List Char
    power-def :
      (n : Int) →
      (word : List Char) →
      zeroZ ≤Z n →
      IfSet
        (intEqual n zeroZ)
        (power word n ≡ [])
        (power word n ≡
          word ++ power word (subtractInt n oneZ))

open PowerModel

ShorterOrEqualBranch :
  {Char : Set} →
  List Char →
  List Char →
  Set
ShorterOrEqualBranch a b =
  let
    o₂ = lengthZ a
    c = drop (toNat o₂) b
  in
  ((zeroZ ≤Z o₂) ∧ (o₂ ≤Z lengthZ b))
  ∧
  (b ≡ a ++ c
   ∧
   (b ≡ a ++ c →
    ((zeroZ ≤Z lengthZ b) ∧ (length c <N length b))
    ∧ a ++ c ≡ c ++ a))

LongerBranch :
  {Char : Set} →
  List Char →
  List Char →
  Set
LongerBranch a b =
  (((zeroZ ≤Z lengthZ a) ∧ (length b <N length a))
   ∨
   (length a ≡ length b
    ∧ (zeroZ ≤Z lengthZ b)
    ∧ (length a <N length b)))
  ∧ b ++ a ≡ a ++ b

DescentObligation :
  {Char : Set} →
  List Char →
  List Char →
  Set
DescentObligation a b =
  lengthZ a ≢ zeroZ →
  lengthZ b ≢ zeroZ →
  IfSet
    (natLessOrEqual (length a) (length b))
    (ShorterOrEqualBranch a b)
    (LongerBranch a b)

PowerConclusion :
  {Char : Set} →
  PowerModel Char →
  List Char →
  List Char →
  List Char →
  Int →
  Int →
  Set
PowerConclusion model a b word ka kb =
  ((zeroZ ≤Z ka) ∧ (a ≡ power model word ka))
  ∧
  ((zeroZ ≤Z kb) ∧ (b ≡ power model word kb))

ShorterOrEqualPremise :
  {Char : Set} →
  PowerModel Char →
  List Char →
  List Char →
  List Char →
  Int →
  Int →
  Set
ShorterOrEqualPremise model a b word ka kb =
  let c = drop (length a) b
  in
  b ≡ a ++ c
  ∧
  Σ Int
    (λ kb₁ →
      (((zeroZ ≤Z ka) ∧ (a ≡ power model word ka))
       ∧
       ((zeroZ ≤Z kb₁) ∧ (c ≡ power model word kb₁)))
      ∧ kb ≡ addInt ka kb₁)

LongerPremise :
  {Char : Set} →
  PowerModel Char →
  List Char →
  List Char →
  List Char →
  Int →
  Int →
  Set
LongerPremise model a b word ka kb =
  ((zeroZ ≤Z kb) ∧ (b ≡ power model word kb))
  ∧
  ((zeroZ ≤Z ka) ∧ (a ≡ power model word ka))

ResultPremise :
  {Char : Set} →
  PowerModel Char →
  List Char →
  List Char →
  List Char →
  Int →
  Int →
  Set
ResultPremise model a b word ka kb =
  IfSet
    (intEqual (lengthZ a) zeroZ)
    (word ≡ b ∧ ka ≡ zeroZ ∧ kb ≡ oneZ)
    (IfSet
      (intEqual (lengthZ b) zeroZ)
      (word ≡ a ∧ ka ≡ oneZ ∧ kb ≡ zeroZ)
      (IfSet
        (natLessOrEqual (length a) (length b))
        (ShorterOrEqualPremise model a b word ka kb)
        (LongerPremise model a b word ka kb)))

ResultObligation :
  {Char : Set} →
  PowerModel Char →
  List Char →
  List Char →
  Set
ResultObligation model a b =
  (word : List _) →
  (ka kb : Int) →
  ResultPremise model a b word ka kb →
  PowerConclusion model a b word ka kb

common-factor'vc : Set₁
common-factor'vc =
  (Char : Set) →
  Inhabited Char →
  (model : PowerModel Char) →
  (a b : List Char) →
  a ++ b ≡ b ++ a →
  DescentObligation a b
  ∧ ResultObligation model a b
