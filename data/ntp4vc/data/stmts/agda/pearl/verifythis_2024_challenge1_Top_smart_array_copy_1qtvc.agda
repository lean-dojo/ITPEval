-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2024_challenge1_Top_smart_array_copy_1qtvc: the
-- verification condition for copying an array through independently shuffled
-- source and destination subsegments while maintaining inverse index maps,
-- followed by an identity-mapped remainder segment. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2024Challenge1TopSmartArrayCopy1VC where

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

CopyTo :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Set
CopyTo src dst ofss ofsd len =
  ValidChunk src ofss len
  ∧ ValidChunk dst ofsd len
  ∧ length src ≡ length dst
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z len) →
    at dst (addInt ofsd i) ≡ at src (addInt ofss i))
  ∧
  ((i : Int) →
    (ofsd ≤Z i ∧ i <Z addInt ofsd len) →
    at dst i ≡ at src (addInt i (subtractInt ofss ofsd)))

CopyPerm :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Array Int →
  Array Int →
  Set
CopyPerm src dst size p invp =
  ValidChunk src zeroZ size
  ∧ length src ≡ length dst
  ∧ PermutationPair size p invp
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z size) →
    (zeroZ ≤Z at p i ∧ at p i <Z size))
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z size) →
    (zeroZ ≤Z at invp i ∧ at invp i <Z size))
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z size) →
    at dst i ≡ at src (at p i))
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z size) →
    at src i ≡ at dst (at invp i))

CopySubsegment :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Set
CopySubsegment src dst s k l j sigma tau p invp =
  let start = multiplyInt s (multiplyInt k l)
      starts = addInt start (multiplyInt (at sigma j) k)
      startd =
        addInt start (multiplyInt (at tau (at sigma j)) k)
  in
  CopyTo src dst starts startd k
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z k) →
    at p (addInt startd i) ≡ addInt starts i)
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z k) →
    at invp (addInt starts i) ≡ addInt startd i)

Frame :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Set
Frame a1 a2 ofs len =
  length a2 ≡ length a1
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z ofs) →
    at a2 i ≡ at a1 i)
  ∧
  ((i : Int) →
    (addInt ofs len ≤Z i ∧ i <Z lengthZ a2) →
    at a2 i ≡ at a1 i)

EarlierSubsegments :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Set
EarlierSubsegments src dst s k l bound sigma tau p invp =
  (j′ : Int) →
  (zeroZ ≤Z j′ ∧ j′ <Z bound) →
  CopySubsegment src dst s k l j′ sigma tau p invp

IdentityLengthSpec : (Int → Array Int) → Set
IdentityLengthSpec identity =
  (l : Int) →
  zeroZ <Z l →
  lengthZ (identity l) ≡ l

IdentityValueSpec : (Int → Array Int) → Set
IdentityValueSpec identity =
  (l i : Int) →
  zeroZ <Z l →
  zeroZ ≤Z i →
  i <Z l →
  at (identity l) i ≡ i

IdentityPermutationSpec : (Int → Array Int) → Set
IdentityPermutationSpec identity =
  (l : Int) →
  zeroZ <Z l →
  PermutationPair l (identity l) (identity l)

IdentityReady :
  {A : Set} →
  (Int → Array Int) →
  Int →
  Array A →
  Set
IdentityReady identity total a =
  let p = identity total
  in
  length p ≡ length a
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z total) →
    at p i ≡ i)
  ∧ PermutationPair total p p

InnerInvariant :
  {A : Set} →
  Array A →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Set
InnerInvariant
  src dst2 dst3 s m startsrc startdst k l j i
  sigma tau p2 invp2 p3 invp3 =
  Frame dst2 dst3 startdst k
  ∧ Frame p2 p3 startdst k
  ∧ Frame invp2 invp3 startsrc k
  ∧ PermutationPair (multiplyInt s m) p3 invp3
  ∧ CopyPerm src dst3 (multiplyInt s m) p3 invp3
  ∧ CopyTo src dst3 startsrc startdst i
  ∧
  ((i′ : Int) →
    (zeroZ ≤Z i′ ∧ i′ <Z i) →
    at p3 (addInt startdst i′) ≡ addInt startsrc i′)
  ∧
  ((i′ : Int) →
    (zeroZ ≤Z i′ ∧ i′ <Z i) →
    at invp3 (addInt startsrc i′) ≡ addInt startdst i′)
  ∧ EarlierSubsegments src dst3 s k
      l
      j sigma tau p3 invp3

InnerUpdateResult :
  {A : Set} →
  Array A →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  A →
  Int →
  Int →
  Set
InnerUpdateResult
  src dst2 dst3 s m startsrc startdst k l j i
  sigma tau p2 invp2 p3 invp3 value sourceIndex destinationIndex =
  let updatedDst = setArray dst3 destinationIndex value
      updatedP = setArray p3 destinationIndex sourceIndex
      updatedInvp = setArray invp3 sourceIndex destinationIndex
  in
  Frame dst2 updatedDst startdst k
  ∧ Frame p2 updatedP startdst k
  ∧ Frame invp2 updatedInvp startsrc k
  ∧ PermutationPair (multiplyInt s m) updatedP updatedInvp
  ∧ CopyPerm src updatedDst (multiplyInt s m) updatedP updatedInvp
  ∧ CopyTo src updatedDst startsrc startdst (addInt i oneZ)
  ∧
  ((i′ : Int) →
    (zeroZ ≤Z i′ ∧ i′ <Z addInt i oneZ) →
    at updatedP (addInt startdst i′) ≡ addInt startsrc i′)
  ∧
  ((i′ : Int) →
    (zeroZ ≤Z i′ ∧ i′ <Z addInt i oneZ) →
    at updatedInvp (addInt startsrc i′) ≡ addInt startdst i′)
  ∧ EarlierSubsegments src updatedDst s k
      l
      j sigma tau updatedP updatedInvp

InnerCellWrite :
  {A : Set} →
  Array A →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Set
InnerCellWrite
  src dst2 dst3 s m startsrc startdst k l j i
  sigma tau p2 invp2 p3 invp3 =
  let sourceIndex = addInt startsrc i
  in
  (zeroZ ≤Z sourceIndex ∧ sourceIndex <Z lengthZ src)
  ∧
  let value = at src sourceIndex
      destinationIndex = addInt startdst i
  in
  (zeroZ ≤Z destinationIndex ∧ destinationIndex <Z lengthZ dst3)
  ∧
  let updatedDst = setArray dst3 destinationIndex value
  in
  (length updatedDst ≡ length dst3 →
   UpdateEquation dst3 updatedDst destinationIndex value →
   (zeroZ ≤Z destinationIndex ∧ destinationIndex <Z lengthZ p3)
   ∧
   let updatedP = setArray p3 destinationIndex sourceIndex
   in
   (length updatedP ≡ length p3 →
    UpdateEquation p3 updatedP destinationIndex sourceIndex →
    (zeroZ ≤Z sourceIndex ∧ sourceIndex <Z lengthZ invp3)
    ∧
    let updatedInvp = setArray invp3 sourceIndex destinationIndex
    in
    (length updatedInvp ≡ length invp3 →
     UpdateEquation invp3 updatedInvp sourceIndex destinationIndex →
     InnerUpdateResult
       src dst2 dst3 s m startsrc startdst k l j i
       sigma tau p2 invp2 p3 invp3
       value sourceIndex destinationIndex)))

InnerStep :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Int →
  Set
InnerStep
  src dst2 s m startsrc startdst k l j sigma tau p2 invp2 o4 =
  (invp3 p3 : Array Int) →
  (dst3 : Array _) →
  length invp3 ≡ length invp2 →
  length p3 ≡ length p2 →
  length dst3 ≡ length dst2 →
  (i : Int) →
  ((zeroZ ≤Z i ∧ i ≤Z o4)
   ∧ InnerInvariant
       src dst2 dst3 s m startsrc startdst k l j i
       sigma tau p2 invp2 p3 invp3) →
  InnerCellWrite
    src dst2 dst3 s m startsrc startdst k l j i
    sigma tau p2 invp2 p3 invp3

InnerExit :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Int →
  Set
InnerExit
  src dst2 s m startsrc startdst k l j sigma tau p2 invp2 o4 =
  (invp3 p3 : Array Int) →
  (dst3 : Array _) →
  length invp3 ≡ length invp2 →
  length p3 ≡ length p2 →
  length dst3 ≡ length dst2 →
  InnerInvariant
    src dst2 dst3 s m startsrc startdst k l j
    (addInt o4 oneZ) sigma tau p2 invp2 p3 invp3 →
  PermutationPair (multiplyInt s m) p3 invp3
  ∧ CopyPerm src dst3 (multiplyInt s m) p3 invp3
  ∧ EarlierSubsegments src dst3 s k
      l
      (addInt j oneZ) sigma tau p3 invp3

InnerLoop :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Int →
  Set
InnerLoop
  src dst2 s m startsrc startdst k l j sigma tau p2 invp2 o4 =
  (zeroZ ≤Z addInt o4 oneZ →
    (Frame dst2 dst2 startdst k
     ∧ Frame p2 p2 startdst k
     ∧ Frame invp2 invp2 startsrc k
     ∧ PermutationPair (multiplyInt s m) p2 invp2
     ∧ CopyPerm src dst2 (multiplyInt s m) p2 invp2
     ∧ CopyTo src dst2 startsrc startdst zeroZ
     ∧
     ((i′ : Int) →
       (zeroZ ≤Z i′ ∧ i′ <Z zeroZ) →
       at p2 (addInt startdst i′) ≡ addInt startsrc i′)
     ∧
     ((i′ : Int) →
       (zeroZ ≤Z i′ ∧ i′ <Z zeroZ) →
       at invp2 (addInt startsrc i′) ≡ addInt startdst i′)
     ∧ EarlierSubsegments src dst2 s k
         l
         j sigma tau p2 invp2)
    ∧
    (InnerStep
       src dst2 s m startsrc startdst k l j
       sigma tau p2 invp2 o4
     ∧ InnerExit
       src dst2 s m startsrc startdst k l j
       sigma tau p2 invp2 o4))
  ∧
  (addInt o4 oneZ <Z zeroZ →
    PermutationPair (multiplyInt s m) p2 invp2
    ∧ CopyPerm src dst2 (multiplyInt s m) p2 invp2
    ∧ EarlierSubsegments src dst2 s k
        l
        (addInt j oneZ) sigma tau p2 invp2)

SubsegmentBody :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Set
SubsegmentBody src dst2 s m k l j sigma tau p2 invp2 =
  (zeroZ ≤Z j ∧ j <Z lengthZ sigma)
  ∧
  let start = multiplyInt s m
      startsrc = addInt start (multiplyInt (at sigma j) k)
  in
  (zeroZ ≤Z j ∧ j <Z lengthZ sigma)
  ∧
  let sigmaAtJ = at sigma j
  in
  (zeroZ ≤Z sigmaAtJ ∧ sigmaAtJ <Z lengthZ tau)
  ∧
  let startdst =
        addInt start (multiplyInt (at tau sigmaAtJ) k)
      o4 = subtractInt k oneZ
  in
  InnerLoop
    src dst2 s m startsrc startdst k l j
    sigma tau p2 invp2 o4

SubsegmentInvariant :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Set
SubsegmentInvariant src dst s m k l bound sigma tau p invp =
  PermutationPair (multiplyInt s m) p invp
  ∧ CopyPerm src dst (multiplyInt s m) p invp
  ∧ EarlierSubsegments src dst s k l bound sigma tau p invp

SubsegmentStep :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Set
SubsegmentStep src dst2 s m k l o2 sigma tau p2 invp2 =
  (j : Int) →
  ((zeroZ ≤Z j ∧ j ≤Z o2)
   ∧ SubsegmentInvariant
       src dst2 s m k l j sigma tau p2 invp2) →
  SubsegmentBody
    src dst2 s m k l j sigma tau p2 invp2

SubsegmentLoop :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Array Int →
  Array Int →
  Set
SubsegmentLoop src dst1 s m k l sigma tau p1 invp1 =
  let o2 = subtractInt l oneZ
  in
  (zeroZ ≤Z addInt o2 oneZ →
    SubsegmentInvariant
      src dst1 s m k l zeroZ sigma tau p1 invp1
    ∧
    ((invp2 p2 : Array Int) →
      (dst2 : Array _) →
      length invp2 ≡ length invp1 →
      length p2 ≡ length p1 →
      length dst2 ≡ length dst1 →
      SubsegmentStep
        src dst2 s m k l o2 sigma tau p2 invp2
      ∧
      (SubsegmentInvariant
         src dst2 s m k l (addInt o2 oneZ)
         sigma tau p2 invp2 →
       PermutationPair
         (multiplyInt (addInt s oneZ) m) p2 invp2
       ∧ CopyPerm src dst2
           (multiplyInt (addInt s oneZ) m) p2 invp2)))
  ∧
  (addInt o2 oneZ <Z zeroZ →
    PermutationPair
      (multiplyInt (addInt s oneZ) m) p1 invp1
    ∧ CopyPerm src dst1
        (multiplyInt (addInt s oneZ) m) p1 invp1)

OuterIterationBody :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Set
OuterIterationBody src dst1 s m k l p1 invp1 =
  zeroZ <Z l
  ∧
  ((sigma invsigma : Array Int) →
    ((length sigma ≡ length invsigma
      ∧ lengthZ invsigma ≡ l)
     ∧ PermutationPair l sigma invsigma) →
    zeroZ <Z l
    ∧
    ((tau invtau : Array Int) →
      ((length tau ≡ length invtau
        ∧ lengthZ invtau ≡ l)
       ∧ PermutationPair l tau invtau) →
      SubsegmentLoop
        src dst1 s m k l sigma tau p1 invp1))

OuterIterationStep :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Set
OuterIterationStep src dst1 o1 m k l s p1 invp1 =
  ((zeroZ ≤Z s ∧ s ≤Z o1)
   ∧ PermutationPair (multiplyInt s m) p1 invp1
   ∧ CopyPerm src dst1 (multiplyInt s m) p1 invp1) →
  OuterIterationBody src dst1 s m k l p1 invp1

FinalCellWrite :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Array Int →
  Array Int →
  Set
FinalCellWrite src dst2 last i p2 invp2 =
  let index = addInt last i
  in
  (zeroZ ≤Z index ∧ index <Z lengthZ src)
  ∧
  let value = at src index
  in
  (zeroZ ≤Z index ∧ index <Z lengthZ dst2)
  ∧
  let updatedDst = setArray dst2 index value
  in
  (length updatedDst ≡ length dst2 →
   UpdateEquation dst2 updatedDst index value →
   (zeroZ ≤Z index ∧ index <Z lengthZ p2)
   ∧
   let updatedP = setArray p2 index index
   in
   (length updatedP ≡ length p2 →
    UpdateEquation p2 updatedP index index →
    (zeroZ ≤Z index ∧ index <Z lengthZ invp2)
    ∧
    let updatedInvp = setArray invp2 index index
    in
    (length updatedInvp ≡ length invp2 →
     UpdateEquation invp2 updatedInvp index index →
     PermutationPair (addInt last (addInt i oneZ))
       updatedP updatedInvp
     ∧ CopyPerm src updatedDst
         (addInt last (addInt i oneZ)) updatedP updatedInvp)))

FinalStep :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Array Int →
  Array Int →
  Set
FinalStep src dst2 last o2 p2 invp2 =
  (i : Int) →
  ((zeroZ ≤Z i ∧ i ≤Z o2)
   ∧ PermutationPair (addInt last i) p2 invp2
   ∧ CopyPerm src dst2 (addInt last i) p2 invp2) →
  FinalCellWrite src dst2 last i p2 invp2

FinalChunk :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Set
FinalChunk src dst last r total p invp =
  let o2 = subtractInt r oneZ
  in
  (zeroZ ≤Z addInt o2 oneZ →
    (PermutationPair (addInt last zeroZ) p invp
     ∧ CopyPerm src dst (addInt last zeroZ) p invp)
    ∧
    ((invp1 p1 : Array Int) →
      (dst1 : Array _) →
      length invp1 ≡ length invp →
      length p1 ≡ length p →
      length dst1 ≡ length dst →
      FinalStep src dst1 last o2 p1 invp1
      ∧
      ((PermutationPair
          (addInt last (addInt o2 oneZ)) p1 invp1
        ∧ CopyPerm src dst1
            (addInt last (addInt o2 oneZ)) p1 invp1) →
       CopyPerm src dst1 total p1 invp1)))
  ∧
  (addInt o2 oneZ <Z zeroZ →
    CopyPerm src dst total p invp)

PositiveOuterLoop :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Set
PositiveOuterLoop src dst o1 m k l q r p invp =
  (PermutationPair (multiplyInt zeroZ m) p invp
   ∧ CopyPerm src dst (multiplyInt zeroZ m) p invp)
  ∧
  ((invp1 p1 : Array Int) →
    (dst1 : Array _) →
    length invp1 ≡ length invp →
    length p1 ≡ length p →
    length dst1 ≡ length dst →
    ((s : Int) →
      OuterIterationStep
        src dst1 o1 m k l s p1 invp1)
    ∧
    ((PermutationPair
        (multiplyInt (addInt o1 oneZ) m) p1 invp1
      ∧ CopyPerm src dst1
          (multiplyInt (addInt o1 oneZ) m) p1 invp1) →
     let last = multiplyInt q m
     in FinalChunk src dst1 last r (lengthZ dst) p1 invp1))

MainLoop :
  {A : Set} →
  Array A →
  Array A →
  Int →
  Int →
  Int →
  Int →
  Array Int →
  Array Int →
  Set
MainLoop src dst k l q r p invp =
  let m = multiplyInt k l
      o1 = subtractInt q oneZ
  in
  (zeroZ ≤Z addInt o1 oneZ →
    PositiveOuterLoop src dst o1 m k l q r p invp)
  ∧
  (addInt o1 oneZ <Z zeroZ →
    let last = multiplyInt q m
    in FinalChunk src dst last r (lengthZ dst) p invp)

smart-array-copy-1'vc : Set₁
smart-array-copy-1'vc =
  (Elt : Set) →
  (identity : Int → Array Int) →
  IdentityLengthSpec identity →
  IdentityValueSpec identity →
  IdentityPermutationSpec identity →
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
  zeroZ <Z lengthZ dst
  ∧
  let total = lengthZ dst
      p = identity total
  in
  IdentityReady identity total dst →
  zeroZ <Z lengthZ dst
  ∧
  let invp = identity total
  in
  IdentityReady identity total dst →
  MainLoop src dst k l q r p invp
