-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2017_odd_even_sort_rearranging_Top_odd_even_sortqtvc:
-- the verification condition for odd-even sorting, preserving permutation,
-- parity-indexed ordering invariants, and entropy-based termination through
-- both sorting passes. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2017OddEvenSortRearrangingTopOddEvenSortQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data Bottom : Set where

record Top : Set where
  constructor top

Not : Set → Set
Not proposition = proposition → Bottom

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

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

natEven : Nat → Bool
natEven zero = true
natEven (suc zero) = false
natEven (suc (suc n)) = natEven n

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

intEven : Int → Bool
intEven (pos n) = natEven n
intEven (negsuc n) = natEven (suc n)

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

EvenZ : Int → Set
EvenZ x = intEven x ≡ true

OddZ : Int → Set
OddZ x = intEven x ≡ false

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

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

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value =
  x ∷ setAt xs n value

maxInt : Int → Int → Int
maxInt x y = IfInt (intLess x y) y x

foldMaximum : Int → List Int → Int
foldMaximum current [] = current
foldMaximum current (x ∷ xs) =
  foldMaximum (maxInt current x) xs

arrayMaximum : List Int → Int
arrayMaximum [] = zeroZ
arrayMaximum (x ∷ xs) = foldMaximum x xs

aux : (Int → Int) → Int → Int → Int
aux values maximum index =
  multiplyInt index (subtractInt maximum (values index))

entropyFrom : List Int → Int → Int → Int
entropyFrom [] maximum index = zeroZ
entropyFrom (x ∷ xs) maximum index =
  addInt
    (multiplyInt index (subtractInt maximum x))
    (entropyFrom xs maximum (addInt index oneZ))

entropy : List Int → Int → Int
entropy values maximum =
  entropyFrom values maximum zeroZ

arrayExchange : List Int → List Int → Int → Int → Set
arrayExchange before after firstIndex secondIndex =
  after ≡
    setAt
      (setAt before
        (toNat firstIndex)
        (nthInt before secondIndex))
      (toNat secondIndex)
      (nthInt before firstIndex)

data Perm {A : Set} : List A → List A → Set where
  permNil :
    Perm [] []

  permKeep :
    {x : A} {xs ys : List A} →
    Perm xs ys →
    Perm (x ∷ xs) (x ∷ ys)

  permSwap :
    (x y : A) →
    (xs : List A) →
    Perm (x ∷ y ∷ xs) (y ∷ x ∷ xs)

  permTrans :
    {xs ys zs : List A} →
    Perm xs ys →
    Perm ys zs →
    Perm xs zs

sortedSub : (Int → Int) → Int → Int → Set
sortedSub values lower upper =
  (i₁ i₂ : Int) →
  ((lower ≤Z i₁) ∧ (i₁ ≤Z i₂) ∧ (i₂ <Z upper)) →
  values i₁ ≤Z values i₂

sorted : List Int → Set
sorted values =
  sortedSub (nthInt values) zeroZ (lengthZ values)

MaximumBound : List Int → Int → Set
MaximumBound values maximum =
  (index : Int) →
  ((zeroZ ≤Z index) ∧ (index <Z lengthZ values)) →
  nthInt values index ≤Z maximum

OddPrefix : List Int → Int → Set
OddPrefix values upper =
  (index : Int) →
  ((zeroZ ≤Z index) ∧ (index <Z upper)) →
  OddZ index →
  nthInt values index ≤Z
    nthInt values (addInt index oneZ)

OddFullPass : List Int → Set
OddFullPass values =
  (index : Int) →
  (((zeroZ ≤Z index) ∧
    (index <Z subtractInt (lengthZ values) oneZ)) ∧
   OddZ index) →
  nthInt values index ≤Z
    nthInt values (addInt index oneZ)

EvenPrefix : List Int → Int → Set
EvenPrefix values upper =
  (index : Int) →
  (((zeroZ ≤Z index) ∧ (index <Z upper)) ∧
   EvenZ index) →
  nthInt values index ≤Z
    nthInt values (addInt index oneZ)

OddInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Bool →
  List Int →
  Set
OddInvariant original anchor maximum index ok current =
  Perm original current ∧
  ((zeroZ ≤Z index) ∧ (index ≤Z lengthZ current)) ∧
  OddZ index ∧
  (ok ≡ true → entropy current maximum ≡ entropy anchor maximum) ∧
  (ok ≡ true → OddPrefix current index) ∧
  (Not (ok ≡ true) →
    entropy current maximum <Z entropy anchor maximum)

EvenInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Bool →
  List Int →
  Set
EvenInvariant original anchor maximum index ok current =
  Perm original current ∧
  ((zeroZ ≤Z index) ∧ (index ≤Z lengthZ current)) ∧
  EvenZ index ∧
  (ok ≡ true → entropy current maximum ≡ entropy anchor maximum) ∧
  (ok ≡ true → OddFullPass current) ∧
  (ok ≡ true → EvenPrefix current index) ∧
  (Not (ok ≡ true) →
    entropy current maximum <Z entropy anchor maximum)

LoopVariantDecrease :
  List Int →
  List Int →
  Int →
  Set
LoopVariantDecrease before after index =
  (zeroZ ≤Z subtractInt (lengthZ before) index) ∧
  (subtractInt (lengthZ after) (addInt index twoZ) <Z
   subtractInt (lengthZ before) index)

OddProgress :
  List Int →
  List Int →
  Int →
  List Int →
  Int →
  Bool →
  List Int →
  Set
OddProgress original anchor maximum before index ok after =
  LoopVariantDecrease before after index ∧
  OddInvariant
    original
    anchor
    maximum
    (addInt index twoZ)
    ok
    after

EvenProgress :
  List Int →
  List Int →
  Int →
  List Int →
  Int →
  Bool →
  List Int →
  Set
EvenProgress original anchor maximum before index ok after =
  LoopVariantDecrease before after index ∧
  EvenInvariant
    original
    anchor
    maximum
    (addInt index twoZ)
    ok
    after

EvenLoopExit :
  List Int →
  List Int →
  Int →
  Bool →
  Bool →
  List Int →
  Set
EvenLoopExit original anchor maximum outerOk currentOk current =
  (zeroZ ≤Z
    addInt
      (entropy anchor maximum)
      (IfInt outerOk zeroZ oneZ)) ∧
  (addInt
      (entropy current maximum)
      (IfInt currentOk zeroZ oneZ)
    <Z
   addInt
      (entropy anchor maximum)
      (IfInt outerOk zeroZ oneZ)) ∧
  Perm original current ∧
  (currentOk ≡ true → sorted current)

EvenComparison :
  List Int →
  List Int →
  Int →
  Bool →
  Int →
  Bool →
  List Int →
  Set
EvenComparison original anchor maximum outerOk index currentOk current =
  let nextIndex = addInt index oneZ
  in
  ((zeroZ ≤Z nextIndex) ∧
   (nextIndex <Z lengthZ current)) ∧
  ((zeroZ ≤Z index) ∧
   (index <Z lengthZ current)) ∧
  IfSet
    (intLess (nthInt current nextIndex) (nthInt current index))
    (let swapIndex = addInt index oneZ
     in
     (nthInt current swapIndex <Z nthInt current index ∧
      zeroZ ≤Z index ∧
      index <Z swapIndex ∧
      swapIndex <Z lengthZ current) ∧
     ((after : List Int) →
      length after ≡ length current →
      (arrayExchange current after index swapIndex ∧
       entropy after maximum <Z entropy current maximum) →
      EvenProgress
        original
        anchor
        maximum
        current
        index
        false
        after))
    (EvenProgress
      original
      anchor
      maximum
      current
      index
      currentOk
      current)

EvenIterationConclusion :
  List Int →
  List Int →
  Int →
  Bool →
  Int →
  Bool →
  List Int →
  Set
EvenIterationConclusion
  original anchor maximum outerOk index currentOk current =
  IfSet
    (intLess index (subtractInt (lengthZ current) oneZ))
    (EvenComparison
      original
      anchor
      maximum
      outerOk
      index
      currentOk
      current)
    (EvenLoopExit
      original
      anchor
      maximum
      outerOk
      currentOk
      current)

EvenLoopObligations :
  List Int →
  List Int →
  Int →
  Bool →
  List Int →
  Set
EvenLoopObligations original anchor maximum outerOk initial =
  (index : Int) →
  (currentOk : Bool) →
  (current : List Int) →
  length current ≡ length initial →
  EvenInvariant
    original anchor maximum index currentOk current →
  EvenIterationConclusion
    original
    anchor
    maximum
    outerOk
    index
    currentOk
    current

EvenPhase :
  List Int →
  List Int →
  Int →
  Bool →
  Bool →
  List Int →
  Set
EvenPhase original anchor maximum outerOk initialOk current =
  EvenInvariant
    original anchor maximum zeroZ initialOk current ∧
  EvenLoopObligations
    original anchor maximum outerOk current

OddComparison :
  List Int →
  List Int →
  Int →
  Int →
  Bool →
  List Int →
  Set
OddComparison original anchor maximum index currentOk current =
  let nextIndex = addInt index oneZ
  in
  ((zeroZ ≤Z nextIndex) ∧
   (nextIndex <Z lengthZ current)) ∧
  ((zeroZ ≤Z index) ∧
   (index <Z lengthZ current)) ∧
  IfSet
    (intLess (nthInt current nextIndex) (nthInt current index))
    (let swapIndex = addInt index oneZ
     in
     (nthInt current swapIndex <Z nthInt current index ∧
      zeroZ ≤Z index ∧
      index <Z swapIndex ∧
      swapIndex <Z lengthZ current) ∧
     ((after : List Int) →
      length after ≡ length current →
      (arrayExchange current after index swapIndex ∧
       entropy after maximum <Z entropy current maximum) →
      OddProgress
        original
        anchor
        maximum
        current
        index
        false
        after))
    (OddProgress
      original
      anchor
      maximum
      current
      index
      currentOk
      current)

OddIterationConclusion :
  List Int →
  List Int →
  Int →
  Bool →
  Int →
  Bool →
  List Int →
  Set
OddIterationConclusion
  original anchor maximum outerOk index currentOk current =
  IfSet
    (intLess index (subtractInt (lengthZ current) oneZ))
    (OddComparison
      original
      anchor
      maximum
      index
      currentOk
      current)
    (EvenPhase
      original
      anchor
      maximum
      outerOk
      currentOk
      current)

OddLoopObligations :
  List Int →
  List Int →
  Int →
  Bool →
  Set
OddLoopObligations original anchor maximum outerOk =
  (index : Int) →
  (currentOk : Bool) →
  (current : List Int) →
  length current ≡ length anchor →
  OddInvariant
    original anchor maximum index currentOk current →
  OddIterationConclusion
    original
    anchor
    maximum
    outerOk
    index
    currentOk
    current

InitialOddState :
  List Int →
  List Int →
  Int →
  Set
InitialOddState original current maximum =
  Perm original current ∧
  ((zeroZ ≤Z oneZ) ∧ (oneZ ≤Z lengthZ current)) ∧
  OddZ oneZ ∧
  OddPrefix current oneZ ∧
  (Not Top → entropy current maximum <Z entropy current maximum)

OddPhase :
  List Int →
  List Int →
  Int →
  Bool →
  Set
OddPhase original current maximum outerOk =
  InitialOddState original current maximum ∧
  OddLoopObligations original current maximum outerOk

OuterBody :
  List Int →
  Int →
  Bool →
  List Int →
  Set
OuterBody original maximum ok current =
  IfSet
    (boolNot ok)
    (OddPhase original current maximum ok)
    (sorted current ∧ Perm original current)

OddEvenSortVC : List Int → Set
OddEvenSortVC original =
  zeroZ <Z lengthZ original →
  let maximum = arrayMaximum original
  in
  MaximumBound original maximum →
  Perm original original ∧
  ((ok : Bool) →
   (current : List Int) →
   length current ≡ length original →
   (Perm original current ∧
    (ok ≡ true → sorted current)) →
   OuterBody original maximum ok current)

odd-even-sort'vc : Set
odd-even-sort'vc =
  (original : List Int) →
  OddEvenSortVC original
