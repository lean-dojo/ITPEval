-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/coincidence_count_CoincidenceCountBag_coincidence_countqtvc: a
-- coincidence-count verification condition for two increasing integer lists,
-- using suffix bags and their multiset-intersection cardinality. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module coincidence_count_CoincidenceCountBag_coincidence_countqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<Z_ _≤Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfBool : Bool → Bool → Bool → Bool
IfBool true when-true when-false = when-true
IfBool false when-true when-false = when-false

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

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

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

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

take : {A : Set} → Nat → List A → List A
take zero xs = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

Bag : Set → Set
Bag A = List A

bagOfSub : List Int → Int → Int → Bag Int
bagOfSub xs lower upper =
  take
    (toNat (subtractInt upper lower))
    (dropList (toNat lower) xs)

bagOf : List Int → Bag Int
bagOf xs = bagOfSub xs zeroZ (lengthZ xs)

dropBag : List Int → Int → Bag Int
dropBag xs lower = bagOfSub xs lower (lengthZ xs)

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) with intEqual sought x
... | true = true
... | false = containsInt sought xs

removeFirst : Int → List Int → List Int
removeFirst sought [] = []
removeFirst sought (x ∷ xs) with intEqual sought x
... | true = xs
... | false = x ∷ removeFirst sought xs

bagIntersection : Bag Int → Bag Int → Bag Int
bagIntersection [] ys = []
bagIntersection (x ∷ xs) ys with containsInt x ys
... | true = x ∷ bagIntersection xs (removeFirst x ys)
... | false = bagIntersection xs ys

bagCard : Bag Int → Int
bagCard xs = natToInt (length xs)

intersectionCard : Bag Int → Bag Int → Int
intersectionCard xs ys = bagCard (bagIntersection xs ys)

Increasing : List Int → Set
Increasing xs =
  (i j : Int) →
  ((zeroZ ≤Z i) ∧ (i <Z j) ∧ (j <Z lengthZ xs)) →
  nthInt xs i ≤Z nthInt xs j

remaining : List Int → List Int → Int → Int → Int
remaining a b i j =
  subtractInt
    (addInt (subtractInt (lengthZ a) i) (lengthZ b))
    j

totalCoincidences : List Int → List Int → Int
totalCoincidences a b =
  intersectionCard (bagOf a) (bagOf b)

suffixCoincidences : List Int → List Int → Int → Int → Int
suffixCoincidences a b i j =
  intersectionCard (dropBag a i) (dropBag b j)

AdvanceLeft :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
AdvanceLeft a b c i j =
  ((zeroZ ≤Z remaining a b i j) ∧
   (remaining a b (addInt i oneZ) j <Z remaining a b i j)) ∧
  ((zeroZ ≤Z addInt i oneZ) ∧
   (addInt i oneZ ≤Z lengthZ a)) ∧
  ((zeroZ ≤Z j) ∧ (j ≤Z lengthZ b)) ∧
  addInt c (suffixCoincidences a b (addInt i oneZ) j) ≡
    totalCoincidences a b

AdvanceRight :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
AdvanceRight a b c i j =
  ((zeroZ ≤Z remaining a b i j) ∧
   (remaining a b i (addInt j oneZ) <Z remaining a b i j)) ∧
  ((zeroZ ≤Z i) ∧ (i ≤Z lengthZ a)) ∧
  ((zeroZ ≤Z addInt j oneZ) ∧
   (addInt j oneZ ≤Z lengthZ b)) ∧
  addInt c (suffixCoincidences a b i (addInt j oneZ)) ≡
    totalCoincidences a b

AdvanceBoth :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
AdvanceBoth a b c i j =
  ((zeroZ ≤Z remaining a b i j) ∧
   (remaining a b (addInt i oneZ) (addInt j oneZ) <Z
    remaining a b i j)) ∧
  ((zeroZ ≤Z addInt i oneZ) ∧
   (addInt i oneZ ≤Z lengthZ a)) ∧
  ((zeroZ ≤Z addInt j oneZ) ∧
   (addInt j oneZ ≤Z lengthZ b)) ∧
  addInt
    (addInt c oneZ)
    (suffixCoincidences a b (addInt i oneZ) (addInt j oneZ))
    ≡ totalCoincidences a b

StepWhenActive :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
StepWhenActive a b c i j =
  ((zeroZ ≤Z j) ∧ (j <Z lengthZ b)) ∧
  ((zeroZ ≤Z i) ∧ (i <Z lengthZ a)) ∧
  IfSet
    (intLess (nthInt a i) (nthInt b j))
    (AdvanceLeft a b c i j)
    (((zeroZ ≤Z j) ∧ (j <Z lengthZ b)) ∧
     ((zeroZ ≤Z i) ∧ (i <Z lengthZ a)) ∧
     IfSet
       (intLess (nthInt b j) (nthInt a i))
       (AdvanceRight a b c i j)
       (AdvanceBoth a b c i j))

LoopPreservation :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
LoopPreservation a b c j i =
  (((zeroZ ≤Z i) ∧ (i ≤Z lengthZ a)) ∧
   ((zeroZ ≤Z j) ∧ (j ≤Z lengthZ b)) ∧
   addInt c (suffixCoincidences a b i j) ≡ totalCoincidences a b) →
  (o1 : Bool) →
  o1 ≡
    IfBool
      (intLess i (lengthZ a))
      (IfBool (intLess j (lengthZ b)) true false)
      false →
  IfSet
    o1
    (StepWhenActive a b c i j)
    (c ≡ totalCoincidences a b)

CoincidenceCountVC : List Int → List Int → Set
CoincidenceCountVC a b =
  Increasing a →
  Increasing b →
  (zeroZ ≤Z zeroZ) ∧
  (zeroZ ≤Z lengthZ a) ∧
  (zeroZ ≤Z zeroZ) ∧
  (zeroZ ≤Z lengthZ b) ∧
  (addInt zeroZ (suffixCoincidences a b zeroZ zeroZ) ≡
   totalCoincidences a b) ∧
  ((c j i : Int) → LoopPreservation a b c j i)

coincidence-count'vc : Set
coincidence-count'vc =
  (a b : List Int) →
  CoincidenceCountVC a b
