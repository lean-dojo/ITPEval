-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2024_challenge1_Top_smart_array_copy_0qtvc: the
-- verification condition for copying an array through shuffled fixed-size
-- subsegments by individual cell updates, followed by a remainder segment.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2024Challenge1TopSmartArrayCopy0VC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

ifValue : {A : Set} → Bool → A → A → A
ifValue true when-true when-false = when-true
ifValue false when-true when-false = when-false

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

record Array (A : Set) : Set where
  constructor array
  field
    length : Nat
    at     : Int → A

open Array public

lengthZ : {A : Set} → Array A → Int
lengthZ a = pos (length a)

updateAt :
  {A : Set} →
  Array A →
  Int →
  A →
  Int →
  A
updateAt old index value query =
  ifValue (intEqual query index) value (at old query)

setArray :
  {A : Set} →
  Array A →
  Int →
  A →
  Array A
setArray old index value =
  array (length old) (updateAt old index value)

UpdateEquation :
  {A : Set} →
  Array A →
  Array A →
  Int →
  A →
  Set
UpdateEquation old new index value =
  (query : Int) →
  at new query ≡ updateAt old index value query

Permutation : Int → Array Int → Set
Permutation l p =
  (zeroZ ≤Z l ∧ l ≤Z lengthZ p)
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z l) →
    (zeroZ ≤Z at p i ∧ at p i <Z l))
  ∧
  ((i j : Int) →
    (zeroZ ≤Z i ∧ i <Z l) →
    (zeroZ ≤Z j ∧ j <Z l) →
    i ≠ j →
    at p i ≠ at p j)

PermutationPair : Int → Array Int → Array Int → Set
PermutationPair l p invp =
  Permutation l p
  ∧ Permutation l invp
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z l) →
    at p (at invp i) ≡ i)
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z l) →
    at invp (at p i) ≡ i)

ValidChunk : {A : Set} → Array A → Int → Int → Set
ValidChunk a ofs len =
  zeroZ ≤Z ofs
  ∧ ofs ≤Z addInt ofs len
  ∧ addInt ofs len ≤Z lengthZ a

Copy :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Set
Copy src dst ofs len =
  ValidChunk src ofs len
  ∧ length src ≡ length dst
  ∧
  ((i : Int) →
    (ofs ≤Z i ∧ i <Z addInt ofs len) →
    at dst i ≡ at src i)

CopiedSubsegments :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Array Int →
  Int →
  Int →
  Set
CopiedSubsegments src dst start sigma k bound =
  (j′ : Int) →
  (zeroZ ≤Z j′ ∧ j′ <Z bound) →
  Copy src dst
    (addInt start (multiplyInt (at sigma j′) k))
    k

AfterSubsegment :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Array Int →
  Int →
  Int →
  Set
AfterSubsegment src dst s m start sigma k j =
  Copy src dst zeroZ (multiplyInt s m)
  ∧ CopiedSubsegments
      src dst start sigma k (addInt j oneZ)

CellWrite :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Array Int →
  Int →
  Int →
  Int →
  Int →
  Set
CellWrite src dst3 s m start sigma k j startj i =
  let index = addInt startj i
      value = at src index
      updated = setArray dst3 index value
  in
  (zeroZ ≤Z index ∧ index <Z lengthZ src)
  ∧
  (zeroZ ≤Z index ∧ index <Z lengthZ dst3)
  ∧
  (length updated ≡ length dst3 →
   UpdateEquation dst3 updated index value →
   Copy src updated zeroZ (multiplyInt s m)
   ∧ CopiedSubsegments src updated start sigma k j
   ∧ Copy src updated startj (addInt i oneZ))

InnerStep :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Array Int →
  Int →
  Int →
  Int →
  Int →
  Set
InnerStep src dst3 s m start sigma k j startj o3 =
  (i : Int) →
  ((zeroZ ≤Z i ∧ i ≤Z o3)
   ∧ Copy src dst3 zeroZ (multiplyInt s m)
   ∧ CopiedSubsegments src dst3 start sigma k j
   ∧ Copy src dst3 startj i) →
  CellWrite src dst3 s m start sigma k j startj i

InnerExit :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Array Int →
  Int →
  Int →
  Int →
  Int →
  Set
InnerExit src dst3 s m start sigma k j startj o3 =
  (Copy src dst3 zeroZ (multiplyInt s m)
   ∧ CopiedSubsegments src dst3 start sigma k j
   ∧ Copy src dst3 startj (addInt o3 oneZ)) →
  AfterSubsegment src dst3 s m start sigma k j

InnerLoop :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Array Int →
  Int →
  Int →
  Int →
  Int →
  Set
InnerLoop src dst2 s m start sigma k j startj o3 =
  (zeroZ ≤Z addInt o3 oneZ →
    (Copy src dst2 zeroZ (multiplyInt s m)
     ∧ CopiedSubsegments src dst2 start sigma k j
     ∧ Copy src dst2 startj zeroZ)
    ∧
    ((dst3 : Array _) →
      length dst3 ≡ length dst2 →
      InnerStep src dst3 s m start sigma k j startj o3
      ∧ InnerExit src dst3 s m start sigma k j startj o3))
  ∧
  (addInt o3 oneZ <Z zeroZ →
    AfterSubsegment src dst2 s m start sigma k j)

SubsegmentBody :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Array Int →
  Int →
  Int →
  Set
SubsegmentBody src dst2 s m start sigma k j =
  (zeroZ ≤Z j ∧ j <Z lengthZ sigma)
  ∧
  let startj =
        addInt start (multiplyInt (at sigma j) k)
      o3 = subtractInt k oneZ
  in InnerLoop src dst2 s m start sigma k j startj o3

SubsegmentStep :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Int →
  Set
SubsegmentStep src dst2 s m start o2 sigma k =
  (j : Int) →
  ((zeroZ ≤Z j ∧ j ≤Z o2)
   ∧ Copy src dst2 zeroZ (multiplyInt s m)
   ∧ CopiedSubsegments src dst2 start sigma k j) →
  SubsegmentBody src dst2 s m start sigma k j

SubsegmentLoop :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Int →
  Set
SubsegmentLoop src dst1 s m start o2 sigma k =
  (zeroZ ≤Z addInt o2 oneZ →
    (Copy src dst1 zeroZ (multiplyInt s m)
     ∧ CopiedSubsegments src dst1 start sigma k zeroZ)
    ∧
    ((dst2 : Array _) →
      length dst2 ≡ length dst1 →
      SubsegmentStep src dst2 s m start o2 sigma k
      ∧
      ((Copy src dst2 zeroZ (multiplyInt s m)
        ∧ CopiedSubsegments
            src dst2 start sigma k (addInt o2 oneZ)) →
        Copy src dst2 zeroZ
          (multiplyInt (addInt s oneZ) m))))
  ∧
  (addInt o2 oneZ <Z zeroZ →
    Copy src dst1 zeroZ
      (multiplyInt (addInt s oneZ) m))

OuterIterationBody :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Set
OuterIterationBody src dst1 s m l k =
  let start = multiplyInt s m
  in
  zeroZ <Z l
  ∧
  ((sigma invsigma : Array Int) →
    ((length sigma ≡ length invsigma
      ∧ lengthZ invsigma ≡ l)
     ∧ PermutationPair l sigma invsigma) →
    let o2 = subtractInt l oneZ
    in SubsegmentLoop src dst1 s m start o2 sigma k)

OuterIterationStep :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
OuterIterationStep src dst1 o1 m l k s =
  ((zeroZ ≤Z s ∧ s ≤Z o1)
   ∧ Copy src dst1 zeroZ (multiplyInt s m)) →
  OuterIterationBody src dst1 s m l k

FinalCellWrite :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Set
FinalCellWrite src dst2 last prefix i =
  let index = addInt last i
      value = at src index
      updated = setArray dst2 index value
  in
  (zeroZ ≤Z index ∧ index <Z lengthZ src)
  ∧
  (zeroZ ≤Z index ∧ index <Z lengthZ dst2)
  ∧
  (length updated ≡ length dst2 →
   UpdateEquation dst2 updated index value →
   Copy src updated zeroZ prefix
   ∧ Copy src updated last (addInt i oneZ))

FinalStep :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Set
FinalStep src dst2 last prefix o2 =
  (i : Int) →
  ((zeroZ ≤Z i ∧ i ≤Z o2)
   ∧ Copy src dst2 zeroZ prefix
   ∧ Copy src dst2 last i) →
  FinalCellWrite src dst2 last prefix i

FinalExit :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Set
FinalExit src dst2 last prefix o2 total =
  (Copy src dst2 zeroZ prefix
   ∧ Copy src dst2 last (addInt o2 oneZ)) →
  Copy src dst2 zeroZ total

FinalChunk :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Set
FinalChunk src dst last r total =
  let o2 = subtractInt r oneZ
      prefix = last
  in
  (zeroZ ≤Z addInt o2 oneZ →
    (Copy src dst zeroZ prefix
     ∧ Copy src dst last zeroZ)
    ∧
    ((dst2 : Array _) →
      length dst2 ≡ length dst →
      FinalStep src dst2 last prefix o2
      ∧ FinalExit src dst2 last prefix o2 total))
  ∧
  (addInt o2 oneZ <Z zeroZ →
    Copy src dst zeroZ total)

PositiveOuterLoopWithRemainder :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
PositiveOuterLoopWithRemainder src dst o1 m l k q r =
  Copy src dst zeroZ (multiplyInt zeroZ m)
  ∧
  ((dst1 : Array _) →
    length dst1 ≡ length dst →
    ((s : Int) → OuterIterationStep src dst1 o1 m l k s)
    ∧
    (Copy src dst1 zeroZ
       (multiplyInt (addInt o1 oneZ) m) →
     let last = multiplyInt q m
     in FinalChunk src dst1 last r (lengthZ dst)))

smart-array-copy-0'vc : Set₁
smart-array-copy-0'vc =
  (Elt : Set) →
  (src dst : Array Elt) →
  (k l q r : Int) →
  length src ≡ length dst →
  zeroZ <Z lengthZ dst →
  zeroZ <Z k →
  zeroZ <Z l →
  zeroZ ≤Z q →
  zeroZ ≤Z r →
  r <Z multiplyInt k l →
  lengthZ dst ≡
    addInt (multiplyInt (multiplyInt q k) l) r →
  let m = multiplyInt k l
      o1 = subtractInt q oneZ
  in
  (zeroZ ≤Z addInt o1 oneZ →
    PositiveOuterLoopWithRemainder src dst o1 m l k q r)
  ∧
  (addInt o1 oneZ <Z zeroZ →
    let last = multiplyInt q m
    in FinalChunk src dst last r (lengthZ dst))
