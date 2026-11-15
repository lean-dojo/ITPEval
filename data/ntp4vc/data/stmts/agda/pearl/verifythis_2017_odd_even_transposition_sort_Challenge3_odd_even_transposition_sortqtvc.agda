-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2017_odd_even_transposition_sort_Challenge3_odd_even_transposition_sortqtvc:
-- the verification condition for sequential odd-even transposition sort,
-- preserving permutation, parity-indexed ordering invariants, swap behavior,
-- inversion-count termination, and final sortedness. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2017OddEvenTranspositionSortChallenge3OddEvenTranspositionSortQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

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

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

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

countLessThan : Int → List Int → Nat
countLessThan pivot [] = zero
countLessThan pivot (x ∷ xs) with intLess x pivot
... | true = suc (countLessThan pivot xs)
... | false = countLessThan pivot xs

inversionsNat : List Int → Nat
inversionsNat [] = zero
inversionsNat (x ∷ xs) =
  countLessThan x xs + inversionsNat xs

inversions : List Int → Int
inversions values = pos (inversionsNat values)

oddIndex : Int → Int
oddIndex halfIndex =
  addInt (multiplyInt twoZ halfIndex) oneZ

evenIndex : Int → Int
evenIndex halfIndex =
  multiplyInt twoZ halfIndex

nextIndex : Int → Int
nextIndex index = addInt index oneZ

advancedIndex : Int → Int
advancedIndex index = addInt index twoZ

oddSorted : List Int → Int → Set
oddSorted values upper =
  (i : Int) →
  zeroZ ≤Z i →
  addInt (multiplyInt twoZ i) twoZ <Z upper →
  nthInt values (addInt (multiplyInt twoZ i) oneZ) ≤Z
    nthInt values (addInt (multiplyInt twoZ i) twoZ)

evenSorted : List Int → Int → Set
evenSorted values upper =
  (i : Int) →
  zeroZ ≤Z i →
  addInt (multiplyInt twoZ i) oneZ <Z upper →
  nthInt values (multiplyInt twoZ i) ≤Z
    nthInt values (addInt (multiplyInt twoZ i) oneZ)

InBounds : List Int → Int → Set
InBounds values index =
  (zeroZ ≤Z index) ∧ (index <Z lengthZ values)

LoopVariantDecrease :
  List Int →
  List Int →
  Int →
  Set
LoopVariantDecrease before after index =
  zeroZ ≤Z subtractInt (lengthZ before) index
  ∧
  subtractInt (lengthZ after) (advancedIndex index) <Z
    subtractInt (lengthZ before) index

OddInvariant :
  List Int →
  List Int →
  Int →
  Bool →
  List Int →
  Set
OddInvariant original anchor halfIndex isSorted current =
  ((zeroZ ≤Z halfIndex) ∧
   (zeroZ ≤Z oddIndex halfIndex))
  ∧
  Perm original current
  ∧
  oddSorted current (oddIndex halfIndex)
  ∧
  IfSet
    isSorted
    (inversions current ≡ inversions anchor)
    (inversions current <Z inversions anchor)

OddAdvancedInvariant :
  List Int →
  List Int →
  Int →
  Bool →
  List Int →
  Set
OddAdvancedInvariant original anchor halfIndex isSorted current =
  let index = oddIndex halfIndex
      nextHalf = addInt halfIndex oneZ
      nextUpper = advancedIndex index
  in
  ((zeroZ ≤Z nextHalf) ∧
   (zeroZ ≤Z nextUpper) ∧
   (nextUpper ≡ oddIndex nextHalf))
  ∧
  Perm original current
  ∧
  oddSorted current nextUpper
  ∧
  IfSet
    isSorted
    (inversions current ≡ inversions anchor)
    (inversions current <Z inversions anchor)

OddProgress :
  List Int →
  List Int →
  List Int →
  Int →
  Bool →
  List Int →
  Set
OddProgress original anchor before halfIndex isSorted after =
  LoopVariantDecrease before after (oddIndex halfIndex)
  ∧
  OddAdvancedInvariant
    original anchor halfIndex isSorted after

EvenInvariant :
  List Int →
  List Int →
  Int →
  Bool →
  List Int →
  Set
EvenInvariant original anchor halfIndex isSorted current =
  let index = evenIndex halfIndex
  in
  ((zeroZ ≤Z halfIndex) ∧ (zeroZ ≤Z index))
  ∧
  zeroZ ≤Z index
  ∧
  Perm original current
  ∧
  (isSorted ≡ true → oddSorted current (lengthZ current))
  ∧
  evenSorted current index
  ∧
  IfSet
    isSorted
    (inversions current ≡ inversions anchor)
    (inversions current <Z inversions anchor)
  ∧
  ((isSorted ≡ true) ∨
   (inversions current <Z inversions anchor))

EvenAdvancedInvariant :
  List Int →
  List Int →
  Int →
  Bool →
  List Int →
  Set
EvenAdvancedInvariant original anchor halfIndex isSorted current =
  let index = evenIndex halfIndex
      nextHalf = addInt halfIndex oneZ
      nextUpper = advancedIndex index
  in
  ((zeroZ ≤Z nextHalf) ∧
   (zeroZ ≤Z nextUpper) ∧
   (nextUpper ≡ evenIndex nextHalf))
  ∧
  zeroZ ≤Z nextUpper
  ∧
  Perm original current
  ∧
  (isSorted ≡ true → oddSorted current (lengthZ current))
  ∧
  evenSorted current nextUpper
  ∧
  IfSet
    isSorted
    (inversions current ≡ inversions anchor)
    (inversions current <Z inversions anchor)
  ∧
  ((isSorted ≡ true) ∨
   (inversions current <Z inversions anchor))

EvenProgress :
  List Int →
  List Int →
  List Int →
  Int →
  Bool →
  List Int →
  Set
EvenProgress original anchor before halfIndex isSorted after =
  LoopVariantDecrease before after (evenIndex halfIndex)
  ∧
  EvenAdvancedInvariant
    original anchor halfIndex isSorted after

LexicographicDecrease :
  List Int →
  Bool →
  Bool →
  List Int →
  Set
LexicographicDecrease anchor outerSorted currentSorted current =
  ((zeroZ ≤Z IfInt outerSorted zeroZ oneZ) ∧
   (IfInt currentSorted zeroZ oneZ <Z
    IfInt outerSorted zeroZ oneZ))
  ∨
  ((IfInt outerSorted zeroZ oneZ ≡
    IfInt currentSorted zeroZ oneZ)
   ∧
   (zeroZ ≤Z inversions anchor)
   ∧
   (inversions current <Z inversions anchor))

EvenLoopExit :
  List Int →
  List Int →
  Bool →
  Bool →
  List Int →
  Set
EvenLoopExit original anchor outerSorted currentSorted current =
  LexicographicDecrease
    anchor outerSorted currentSorted current
  ∧
  Perm original current
  ∧
  (currentSorted ≡ true → sorted current)

EvenComparison :
  List Int →
  List Int →
  Bool →
  Int →
  Bool →
  List Int →
  Set
EvenComparison
  original anchor outerSorted halfIndex currentSorted current =
  let index = evenIndex halfIndex
      o₁ = nextIndex index
  in
  InBounds current o₁
  ∧
  InBounds current index
  ∧
  IfSet
    (intLess (nthInt current o₁) (nthInt current index))
    (let o₂ = nextIndex index
     in
     (InBounds current index ∧ InBounds current o₂)
     ∧
     ((after : List Int) →
      length after ≡ length current →
      arrayExchange current after index o₂ →
      EvenProgress
        original anchor current halfIndex false after))
    (EvenProgress
      original anchor current halfIndex currentSorted current)

EvenIterationConclusion :
  List Int →
  List Int →
  Bool →
  Int →
  Bool →
  List Int →
  Set
EvenIterationConclusion
  original anchor outerSorted halfIndex currentSorted current =
  let index = evenIndex halfIndex
  in
  IfSet
    (intLess index (subtractInt (lengthZ current) oneZ))
    (EvenComparison
      original anchor outerSorted
      halfIndex currentSorted current)
    (EvenLoopExit
      original anchor outerSorted currentSorted current)

EvenLoopObligations :
  List Int →
  List Int →
  Bool →
  List Int →
  Set
EvenLoopObligations original anchor outerSorted initial =
  (halfIndex : Int) →
  (currentSorted : Bool) →
  (current : List Int) →
  length current ≡ length initial →
  EvenInvariant
    original anchor halfIndex currentSorted current →
  EvenIterationConclusion
    original anchor outerSorted
    halfIndex currentSorted current

InitialEvenState :
  List Int →
  List Int →
  List Int →
  Bool →
  Set
InitialEvenState original anchor current currentSorted =
  ((zeroZ ≤Z zeroZ) ∧
   (zeroZ ≤Z zeroZ) ∧
   (zeroZ ≡ evenIndex zeroZ))
  ∧
  zeroZ ≤Z zeroZ
  ∧
  Perm original current
  ∧
  (currentSorted ≡ true → oddSorted current (lengthZ current))
  ∧
  evenSorted current zeroZ
  ∧
  IfSet
    currentSorted
    (inversions current ≡ inversions anchor)
    (inversions current <Z inversions anchor)
  ∧
  ((currentSorted ≡ true) ∨
   (inversions current <Z inversions anchor))

EvenPhase :
  List Int →
  List Int →
  List Int →
  Bool →
  Bool →
  Set
EvenPhase original anchor initial outerSorted currentSorted =
  InitialEvenState original anchor initial currentSorted
  ∧
  EvenLoopObligations original anchor outerSorted initial

OddComparison :
  List Int →
  List Int →
  Int →
  Bool →
  List Int →
  Set
OddComparison original anchor halfIndex currentSorted current =
  let index = oddIndex halfIndex
      o₁ = nextIndex index
  in
  InBounds current o₁
  ∧
  InBounds current index
  ∧
  IfSet
    (intLess (nthInt current o₁) (nthInt current index))
    (let o₂ = nextIndex index
     in
     (InBounds current index ∧ InBounds current o₂)
     ∧
     ((after : List Int) →
      length after ≡ length current →
      arrayExchange current after index o₂ →
      OddProgress
        original anchor current halfIndex false after))
    (OddProgress
      original anchor current halfIndex currentSorted current)

OddIterationConclusion :
  List Int →
  List Int →
  Bool →
  Int →
  Bool →
  List Int →
  Set
OddIterationConclusion
  original anchor outerSorted halfIndex currentSorted current =
  let index = oddIndex halfIndex
  in
  IfSet
    (intLess index (subtractInt (lengthZ current) oneZ))
    (OddComparison
      original anchor halfIndex currentSorted current)
    (EvenPhase
      original anchor current outerSorted currentSorted)

OddLoopObligations :
  List Int →
  List Int →
  Bool →
  Set
OddLoopObligations original anchor outerSorted =
  (halfIndex : Int) →
  (currentSorted : Bool) →
  (current : List Int) →
  length current ≡ length anchor →
  OddInvariant
    original anchor halfIndex currentSorted current →
  OddIterationConclusion
    original anchor outerSorted
    halfIndex currentSorted current

InitialOddState :
  List Int →
  List Int →
  Set
InitialOddState original current =
  ((zeroZ ≤Z zeroZ) ∧
   (zeroZ ≤Z oneZ) ∧
   (oneZ ≡ oddIndex zeroZ))
  ∧
  Perm original current
  ∧
  oddSorted current oneZ
  ∧
  (Not Top → inversions current <Z inversions current)

OddPhase :
  List Int →
  List Int →
  Bool →
  Set
OddPhase original current outerSorted =
  InitialOddState original current
  ∧
  OddLoopObligations original current outerSorted

OuterBody :
  List Int →
  Bool →
  List Int →
  Set
OuterBody original isSorted current =
  IfSet
    (boolNot isSorted)
    (OddPhase original current isSorted)
    (sorted current ∧ Perm original current)

OddEvenTranspositionSortVC : List Int → Set
OddEvenTranspositionSortVC original =
  Perm original original
  ∧
  ((isSorted : Bool) →
   (current : List Int) →
   length current ≡ length original →
   (Perm original current
    ∧
    (isSorted ≡ true → sorted current)) →
   OuterBody original isSorted current)

odd-even-transposition-sort'vc : Set
odd-even-transposition-sort'vc =
  (original : List Int) →
  OddEvenTranspositionSortVC original
