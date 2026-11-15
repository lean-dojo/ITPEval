-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/sumrange_CumulativeArray_createqtvc: the cumulative-sum array
-- creation verification condition, including initialization, loop-invariant
-- preservation after each array update, and the final cumulative-array
-- specification. This file contains no proof.

{-# OPTIONS --safe #-}

module sumrange_CumulativeArray_createqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

nthFunction : List Int → Int → Int
nthFunction xs index = nthInt xs index

updateFunction :
  (Int → Int) →
  Int →
  Int →
  Int →
  Int
updateFunction values index value query =
  IfInt (intEqual query index) value (values query)

sumFrom : List Int → Nat → Nat → Int
sumFrom values start zero = zeroZ
sumFrom values start (suc count) =
  addInt
    (nthDefault zeroZ start values)
    (sumFrom values (suc start) count)

sumRange : List Int → Int → Int → Int
sumRange values lower upper =
  sumFrom
    values
    (toNat lower)
    (toNat (subtractInt upper lower))

PrefixCorrect :
  List Int →
  List Int →
  Int →
  Set
PrefixCorrect source cumulative upper =
  (k : Int) →
  ((zeroZ ≤Z k) ∧ (k <Z upper)) →
  nthInt cumulative k ≡ sumRange source zeroZ k

IsCumulativeArrayFor :
  List Int →
  List Int →
  Set
IsCumulativeArrayFor cumulative source =
  (lengthZ cumulative ≡ addInt (lengthZ source) oneZ) ∧
  ((i : Int) →
    ((zeroZ ≤Z i) ∧ (i <Z lengthZ cumulative)) →
    nthInt cumulative i ≡ sumRange source zeroZ i)

ZeroInitialized : List Int → Int → Set
ZeroInitialized values upper =
  (i : Int) →
  ((zeroZ ≤Z i) ∧ (i <Z upper)) →
  nthInt values i ≡ zeroZ

UpdateStep :
  List Int →
  List Int →
  Int →
  Set
UpdateStep source cumulative i =
  let
    previous = subtractInt i oneZ
    nextValue =
      addInt
        (nthInt cumulative previous)
        (nthInt source previous)
    updated = setAt cumulative (toNat i) nextValue
  in
  ((zeroZ ≤Z previous) ∧
   (previous <Z lengthZ source))
  ∧
  ((zeroZ ≤Z previous) ∧
   (previous <Z lengthZ cumulative))
  ∧
  ((zeroZ ≤Z i) ∧
   (i <Z lengthZ cumulative))
  ∧
  ((length updated ≡ length cumulative) →
   ((query : Int) →
     nthFunction updated query ≡
       updateFunction
         (nthFunction cumulative)
         i
         nextValue
         query) →
   PrefixCorrect source updated (addInt i oneZ))

LoopObligations :
  List Int →
  List Int →
  Int →
  Set
LoopObligations source initial l =
  (current : List Int) →
  length current ≡ length initial →
  (((i : Int) →
    (((oneZ ≤Z i) ∧ (i ≤Z l)) ∧
     PrefixCorrect source current i) →
    UpdateStep source current i)
   ∧
   (PrefixCorrect source current (addInt l oneZ) →
    IsCumulativeArrayFor current source))

NonemptyBranch :
  List Int →
  List Int →
  Int →
  Set
NonemptyBranch source initial l =
  oneZ ≤Z addInt l oneZ →
  PrefixCorrect source initial oneZ ∧
  LoopObligations source initial l

CreateVC : List Int → Set
CreateVC source =
  let
    l = lengthZ source
    allocatedLength = addInt l oneZ
  in
  (zeroZ ≤Z allocatedLength)
  ∧
  ((initial : List Int) →
    (ZeroInitialized initial allocatedLength ∧
     (lengthZ initial ≡ allocatedLength)) →
    (NonemptyBranch source initial l
     ∧
     (addInt l oneZ <Z oneZ →
      IsCumulativeArrayFor initial source)))

create'vc : Set
create'vc =
  (source : List Int) →
  CreateVC source
