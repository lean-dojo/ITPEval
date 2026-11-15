-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/decrease1_Decrease1_search_recqtvc: a recursive-search verification
-- condition for a list whose adjacent values decrease by at most one,
-- returning its first zero at or after a starting index or reporting absence.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module decrease1_Decrease1_search_recqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

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

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

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

zeroZ oneZ minusOneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
minusOneZ = negsuc zero

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

InBounds : List Int → Int → Set
InBounds a index =
  zeroZ ≤Z index ∧ index <Z lengthZ a

decrease1 : List Int → Set
decrease1 a =
  (index : Int) →
  (zeroZ ≤Z index ∧
   index <Z subtractInt (lengthZ a) oneZ) →
  subtractInt (nthInt a index) oneZ
    ≤Z nthInt a (addInt index oneZ)

RecursiveCallObligation :
  List Int →
  Int →
  Int →
  Set
RecursiveCallObligation a current next =
  (zeroZ ≤Z subtractInt (lengthZ a) current ∧
   subtractInt (lengthZ a) next
     <Z subtractInt (lengthZ a) current) ∧
  decrease1 a ∧
  zeroZ ≤Z next

SearchPost :
  List Int →
  Int →
  Int →
  Set
SearchPost a lower result =
  (result ≡ minusOneZ ∧
   ((j : Int) →
    (lower ≤Z j ∧ j <Z lengthZ a) →
    Not (nthInt a j ≡ zeroZ)))
  ∨
  ((lower ≤Z result ∧ result <Z lengthZ a) ∧
   nthInt a result ≡ zeroZ ∧
   ((j : Int) →
    (lower ≤Z j ∧ j <Z result) →
    Not (nthInt a j ≡ zeroZ)))

InitialObligation :
  List Int →
  Int →
  Set
InitialObligation a i =
  i <Z lengthZ a →
  InBounds a i ∧
  (Not (nthInt a i ≡ zeroZ) →
   InBounds a i ∧
   IfSet
     (intLess zeroZ (nthInt a i))
     (InBounds a i ∧
      RecursiveCallObligation
        a
        i
        (addInt i (nthInt a i)))
     (RecursiveCallObligation
       a
       i
       (addInt i oneZ)))

ResultPremise :
  List Int →
  Int →
  Int →
  Set
ResultPremise a i result =
  IfSet
    (intLess i (lengthZ a))
    (IfSet
      (intEqual (nthInt a i) zeroZ)
      (result ≡ i)
      (IfSet
        (intLess zeroZ (nthInt a i))
        (SearchPost a (addInt i (nthInt a i)) result)
        (SearchPost a (addInt i oneZ) result)))
    (result ≡ minusOneZ)

SearchRecVC : List Int → Int → Set
SearchRecVC a i =
  decrease1 a →
  zeroZ ≤Z i →
  InitialObligation a i ∧
  ((result : Int) →
   ResultPremise a i result →
   SearchPost a i result)

search-rec'vc : Set
search-rec'vc =
  (a : List Int) →
  (i : Int) →
  SearchRecVC a i
