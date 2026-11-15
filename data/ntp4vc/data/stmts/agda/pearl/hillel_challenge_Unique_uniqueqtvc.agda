-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/hillel_challenge_Unique_uniqueqtvc: the verification condition for
-- constructing a duplicate-free list with exactly the values of an input
-- integer list while maintaining finite-map and prefix invariants. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module hillel_challenge_Unique_uniqueqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≤Z_ _<Z_
infix 3 _↔_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

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

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthInt : {A : Set} → List A → Int
lengthInt xs = pos (length xs)

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

nthNat : List Int → Nat → Int
nthNat [] _ = zeroZ
nthNat (x ∷ _) zero = x
nthNat (_ ∷ xs) (suc n) = nthNat xs n

nth : List Int → Int → Int
nth xs i = nthNat xs (toNat i)

setAt : List Int → Nat → Int → List Int
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

setList : List Int → Int → Int → List Int
setList xs i value = setAt xs (toNat i) value

updateFunction :
  (Int → Int) →
  Int →
  Int →
  Int →
  Int
updateFunction f key value argument with intEqual argument key
... | true = value
... | false = f argument

data FinMap : Set where
  emptyMap : FinMap
  insertMap : Int → FinMap → FinMap

contains : Int → FinMap → Bool
contains key emptyMap = false
contains key (insertMap stored rest) with intEqual key stored
... | true = true
... | false = contains key rest

Mem : Int → List Int → Int → Set
Mem x a i =
  Σ Int
    (λ j →
      (zeroZ ≤Z j ∧ j <Z i) ∧
      nth a j ≡ x)

UniquePrefix : List Int → Int → Set
UniquePrefix values upper =
  (i j : Int) →
  (zeroZ ≤Z i ∧ i <Z j ∧ j <Z upper) →
  Not (nth values i ≡ nth values j)

SamePrefixValues :
  List Int →
  List Int →
  Int →
  Int →
  Set
SamePrefixValues a result inputUpper resultUpper =
  (x : Int) →
  Mem x a inputUpper ↔ Mem x result resultUpper

MapMatchesPrefix :
  List Int →
  FinMap →
  Int →
  Set
MapMatchesPrefix a h upper =
  (x : Int) →
  Mem x a upper ↔ contains x h ≡ true

IndexInList : Int → List Int → Set
IndexInList i values =
  zeroZ ≤Z i ∧ i <Z lengthInt values

LoopInvariant :
  List Int →
  Int →
  FinMap →
  List Int →
  Int →
  Int →
  Set
LoopInvariant a o1 h1 res1 len i =
  (zeroZ ≤Z i ∧ i ≤Z o1) ∧
  (zeroZ ≤Z len ∧ len ≤Z i) ∧
  MapMatchesPrefix a h1 i ∧
  SamePrefixValues a res1 i len ∧
  UniquePrefix res1 len

NextInvariant :
  List Int →
  FinMap →
  List Int →
  Int →
  Int →
  Set
NextInvariant a h values inputUpper resultUpper =
  (zeroZ ≤Z resultUpper ∧ resultUpper ≤Z inputUpper) ∧
  MapMatchesPrefix a h inputUpper ∧
  SamePrefixValues a values inputUpper resultUpper ∧
  UniquePrefix values resultUpper

FreshValueBranch :
  List Int →
  List Int →
  FinMap →
  Int →
  Int →
  Set
FreshValueBranch a res1 h1 len i =
  IndexInList i a ∧
  ((h2 : FinMap) →
    h2 ≡ insertMap (nth a i) h1 →
    IndexInList i a ∧
    (let o2 = nth a i
         updated = setList res1 len o2
     in
     (zeroZ ≤Z len ∧ len <Z lengthInt res1) ∧
     (length updated ≡ length res1 →
      (λ index → nth updated index) ≡
        updateFunction (λ index → nth res1 index) len o2 →
      NextInvariant
        a h2 updated
        (addInt i oneZ)
        (addInt len oneZ))))

RepeatedValueBranch :
  List Int →
  List Int →
  FinMap →
  Int →
  Int →
  Set
RepeatedValueBranch a res1 h1 len i =
  NextInvariant a h1 res1 (addInt i oneZ) len

LoopStep :
  List Int →
  List Int →
  FinMap →
  Int →
  Int →
  Set
LoopStep a res1 h1 len i =
  IndexInList i a ∧
  IfSet
    (notBool (contains (nth a i) h1))
    (FreshValueBranch a res1 h1 len i)
    (RepeatedValueBranch a res1 h1 len i)

ExtractionResult :
  List Int →
  List Int →
  Int →
  Set
ExtractionResult a res1 len =
  (result : List Int) →
  (lengthInt result ≡ len ∧
   ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z len) →
    nth result i ≡ nth res1 (addInt zeroZ i))) →
  SamePrefixValues
    a result
    (lengthInt a)
    (lengthInt result) ∧
  UniquePrefix result (lengthInt result)

FinalExtraction :
  List Int →
  Int →
  List Int →
  FinMap →
  Int →
  Set
FinalExtraction a o1 res1 h1 len =
  NextInvariant
    a h1 res1
    (addInt o1 oneZ)
    len →
  (zeroZ ≤Z zeroZ ∧
   zeroZ ≤Z len ∧
   addInt zeroZ len ≤Z lengthInt res1) ∧
  ExtractionResult a res1 len

LoopPackage :
  List Int →
  List Int →
  Int →
  Set
LoopPackage a res o1 =
  (len : Int) →
  (res1 : List Int) →
  (h1 : FinMap) →
  length res1 ≡ length res →
  ((i : Int) →
    LoopInvariant a o1 h1 res1 len i →
    LoopStep a res1 h1 len i) ∧
  FinalExtraction a o1 res1 h1 len

InitialState :
  List Int →
  List Int →
  FinMap →
  Set
InitialState a res h =
  zeroZ ≤Z zeroZ ∧
  MapMatchesPrefix a h zeroZ ∧
  SamePrefixValues a res zeroZ zeroZ ∧
  UniquePrefix res zeroZ

PositiveRangeCase :
  List Int →
  List Int →
  FinMap →
  Int →
  Set
PositiveRangeCase a res h o1 =
  zeroZ ≤Z addInt o1 oneZ →
  InitialState a res h ∧
  LoopPackage a res o1

ZeroLengthExtraction :
  List Int →
  List Int →
  Set
ZeroLengthExtraction a res =
  (zeroZ ≤Z zeroZ ∧
   zeroZ ≤Z zeroZ ∧
   addInt zeroZ zeroZ ≤Z lengthInt res) ∧
  ((result : List Int) →
    (lengthInt result ≡ zeroZ ∧
     ((i : Int) →
      (zeroZ ≤Z i ∧ i <Z zeroZ) →
      nth result i ≡ nth res (addInt zeroZ i))) →
    SamePrefixValues
      a result
      (lengthInt a)
      (lengthInt result) ∧
    UniquePrefix result (lengthInt result))

NegativeRangeCase :
  List Int →
  List Int →
  Int →
  Set
NegativeRangeCase a res o1 =
  addInt o1 oneZ <Z zeroZ →
  ZeroLengthExtraction a res

ResultBufferCondition :
  List Int →
  Int →
  Set
ResultBufferCondition res n =
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z n) →
    nth res i ≡ zeroZ) ∧
  lengthInt res ≡ n

UniqueVC : List Int → Set
UniqueVC a =
  let n = lengthInt a
  in
  (h : FinMap) →
  h ≡ emptyMap →
  zeroZ ≤Z n ∧
  ((res : List Int) →
    ResultBufferCondition res n →
    let o1 = subtractInt n oneZ
    in
    PositiveRangeCase a res h o1 ∧
    NegativeRangeCase a res o1)

unique'vc : Set
unique'vc = (a : List Int) → UniqueVC a
