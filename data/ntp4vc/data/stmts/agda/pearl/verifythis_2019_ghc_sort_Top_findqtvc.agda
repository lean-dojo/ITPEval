-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2019_ghc_sort_Top_findqtvc: the recursive verification
-- condition for finding an integer value in a nonempty half-open sequence
-- interval with a positive occurrence count. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2019GhcSortTopFindVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

take : {A : Set} → Nat → List A → List A
take zero _ = []
take (suc _) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

countList : Int → List Int → Nat
countList value [] = zero
countList value (x ∷ xs) with intEqual value x
... | true = suc (countList value xs)
... | false = countList value xs

interval : {A : Set} → List A → Int → Int → List A
interval xs lower upper =
  take
    (toNat (subtractInt upper lower))
    (drop (toNat lower) xs)

OccurrenceAtLeastOne : Int → List Int → Int → Int → Set
OccurrenceAtLeastOne value xs lower upper =
  oneZ ≤Z natToInt (countList value (interval xs lower upper))

RecursiveCallObligation : Int → Int → List Int → Int → Set
RecursiveCallObligation start finish xs value =
  let next = addInt start oneZ
  in
  ((zeroZ ≤Z subtractInt finish start) ∧
   (subtractInt finish next <Z subtractInt finish start)) ∧
  ((zeroZ ≤Z next) ∧
   (next <Z finish) ∧
   (finish ≤Z lengthZ xs)) ∧
  OccurrenceAtLeastOne value xs next finish

ResultPremise : Int → Int → List Int → Int → Int → Int → Set
ResultPremise start finish xs value first result =
  IfSet
    (intEqual first value)
    (result ≡ start)
    (((addInt start oneZ ≤Z result) ∧
      (result <Z finish)) ∧
     (nthInt xs result ≡ value))

ResultPostcondition : Int → Int → List Int → Int → Int → Set
ResultPostcondition start finish xs value result =
  ((start ≤Z result) ∧
   (result <Z finish)) ∧
  (nthInt xs result ≡ value)

FindConclusion : Int → Int → List Int → Int → Set
FindConclusion start finish xs value =
  let first = nthInt xs start
  in
  (Not (first ≡ value) →
   RecursiveCallObligation start finish xs value) ∧
  ((result : Int) →
   ResultPremise start finish xs value first result →
   ResultPostcondition start finish xs value result)

find'vc : Set
find'vc =
  (start finish : Int) →
  (xs : List Int) →
  (value : Int) →
  zeroZ ≤Z start →
  start <Z finish →
  finish ≤Z lengthZ xs →
  OccurrenceAtLeastOne value xs start finish →
  FindConclusion start finish xs value
