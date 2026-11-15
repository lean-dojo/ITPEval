-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_dll_to_bst_Top_dll_to_bst_recqtvc: the recursive
-- verification condition for converting a finite-map doubly linked list
-- segment into a balanced binary tree. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021DllToBstTopDllToBstRecVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_ _≢_ _∈_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≢_ : {A : Set} → A → A → Set
x ≢ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

ifValue : {A : Set} → Bool → A → A → A
ifValue true when-true when-false = when-true
ifValue false when-true when-false = when-false

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

maxInt : Int → Int → Int
maxInt x y with intLess x y
... | true = y
... | false = x

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

-- Why3's ComputerDivision.div by positive two truncates toward zero.
tdivTwo : Int → Int
tdivTwo (pos n) = pos (halfNat n)
tdivTwo (negsuc n) = negative (halfNat (suc n))

powerNat : Int → Nat → Int
powerNat base zero = pos (suc zero)
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent = powerNat base (toNat exponent)

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

record FiniteMap (A : Set) : Set where
  constructor finiteMap
  field
    keys     : List A
    contents : A → A

open FiniteMap

domainEqual : {A : Set} → FiniteMap A → FiniteMap A → Set
domainEqual {A = A} leftMap rightMap =
  (key : A) → (key ∈ keys leftMap) ↔ (key ∈ keys rightMap)

mapUpdatedAt :
  {A : Set} →
  FiniteMap A →
  FiniteMap A →
  A →
  A →
  Set
mapUpdatedAt {A = A} newer older key value =
  ((query : A) →
    (query ∈ keys newer) ↔
      ((query ≡ key) ∨ (query ∈ keys older)))
  ∧ contents newer key ≡ value
  ∧ ((query : A) →
      query ≢ key →
      query ∈ keys older →
      contents newer query ≡ contents older query)

record Signature : Set₁ where
  field
    Loc          : Set
    null         : Loc
    Store        : Set
    storeDefault : Store
    toFMap       : Store → FiniteMap Loc

open Signature

nthLoc :
  (sig : Signature) →
  List (Loc sig) →
  Int →
  Loc sig
nthLoc sig xs index =
  nthDefault (null sig) (toNat index) xs

nodeAt :
  (sig : Signature) →
  List (Loc sig) →
  Int →
  Loc sig
nodeAt sig s index =
  ifValue
    (intEqual index (lengthZ s))
    (null sig)
    (nthLoc sig s index)

valid :
  (sig : Signature) →
  FiniteMap (Loc sig) →
  FiniteMap (Loc sig) →
  List (Loc sig) →
  Set
valid sig prev next s =
  (i : Int) →
  (zeroZ ≤Z i ∧ i <Z lengthZ s) →
  nthLoc sig s i ≢ null sig
  ∧ nthLoc sig s i ∈ keys prev
  ∧ nthLoc sig s i ∈ keys next
  ∧ ((j : Int) →
      (i <Z j ∧ j <Z lengthZ s) →
      nthLoc sig s i ≢ nthLoc sig s j)

dll :
  (sig : Signature) →
  FiniteMap (Loc sig) →
  FiniteMap (Loc sig) →
  List (Loc sig) →
  Loc sig →
  Int →
  Int →
  Set
dll sig prev next s head lo hi =
  valid sig prev next s
  ∧ (zeroZ ≤Z lo ∧ lo ≤Z hi ∧ hi ≤Z lengthZ s)
  ∧ head ≡ nodeAt sig s lo
  ∧ ((i : Int) →
      (lo ≤Z i ∧ i <Z subtractInt hi oneZ) →
      contents next (nthLoc sig s i) ≡
        nthLoc sig s (addInt i oneZ))
  ∧ ((i : Int) →
      (lo <Z i ∧ i <Z hi) →
      contents prev (nthLoc sig s i) ≡
        nthLoc sig s (subtractInt i oneZ))
  ∧ (lo <Z hi →
      contents next
        (nthLoc sig s (subtractInt hi oneZ))
      ≡ nodeAt sig s hi)
  ∧ (lo <Z hi →
      contents prev (nthLoc sig s lo)
      ≡ ifValue
          (intEqual lo zeroZ)
          (null sig)
          (nthLoc sig s (subtractInt lo oneZ)))

data Tree : Set where
  Empty : Tree
  Node  : Tree → Int → Tree → Tree

height : Tree → Int
height Empty = zeroZ
height (Node left position right) =
  addInt oneZ (maxInt (height left) (height right))

tree :
  (sig : Signature) →
  FiniteMap (Loc sig) →
  FiniteMap (Loc sig) →
  List (Loc sig) →
  Loc sig →
  Tree →
  Int →
  Int →
  Set
tree sig prev next s root Empty lo hi =
  valid sig prev next s
  ∧ (zeroZ ≤Z lo ∧ lo ≤Z hi ∧ hi ≤Z lengthZ s)
  ∧ (root ≡ null sig ∧ lo ≡ hi)
tree sig prev next s root (Node left position right) lo hi =
  valid sig prev next s
  ∧ (zeroZ ≤Z lo ∧ lo ≤Z hi ∧ hi ≤Z lengthZ s)
  ∧ (lo ≤Z position ∧ position <Z hi)
  ∧ root ≡ nthLoc sig s position
  ∧ tree
      sig
      prev
      next
      s
      (contents prev root)
      left
      lo
      position
  ∧ tree
      sig
      prev
      next
      s
      (contents next root)
      right
      (addInt position oneZ)
      hi

lookupAgreement :
  (sig : Signature) →
  FiniteMap (Loc sig) →
  FiniteMap (Loc sig) →
  List (Loc sig) →
  Int →
  Int →
  Set
lookupAgreement sig current original s lower upper =
  (i : Int) →
  (lower ≤Z i ∧ i <Z upper) →
  contents current (nthLoc sig s i) ≡
    contents original (nthLoc sig s i)

heightBound : Tree → Int → Set
heightBound result n =
  let h = height result
  in
  powerInt twoZ (subtractInt h oneZ) ≤Z n
  ∧ n <Z powerInt twoZ h

recursivePost :
  (sig : Signature) →
  Store sig →
  Store sig →
  List (Loc sig) →
  Int →
  Int →
  Store sig →
  Store sig →
  Loc sig →
  Tree →
  Set
recursivePost
  sig originalPrev originalNext s lo count currentNext currentPrev root result =
  tree
    sig
    (toFMap sig currentPrev)
    (toFMap sig currentNext)
    s
    root
    result
    lo
    (addInt lo count)
  ∧ domainEqual
      (toFMap sig currentPrev)
      (toFMap sig originalPrev)
  ∧ domainEqual
      (toFMap sig currentNext)
      (toFMap sig originalNext)
  ∧ lookupAgreement
      sig
      (toFMap sig currentPrev)
      (toFMap sig originalPrev)
      s
      zeroZ
      lo
  ∧ lookupAgreement
      sig
      (toFMap sig currentPrev)
      (toFMap sig originalPrev)
      s
      (addInt lo count)
      (lengthZ s)
  ∧ lookupAgreement
      sig
      (toFMap sig currentNext)
      (toFMap sig originalNext)
      s
      zeroZ
      lo
  ∧ lookupAgreement
      sig
      (toFMap sig currentNext)
      (toFMap sig originalNext)
      s
      (addInt lo count)
      (lengthZ s)
  ∧ (zeroZ <Z count → heightBound result count)

finalRecursiveResult :
  (sig : Signature) →
  Store sig →
  Store sig →
  List (Loc sig) →
  Int →
  Int →
  Int →
  Store sig →
  Store sig →
  Tree →
  Tree →
  Loc sig →
  Set
finalRecursiveResult
  sig originalPrev originalNext s ihead n nl finalNext finalPrev leftTree rightTree root =
  let o₁ = subtractInt (subtractInt n nl) oneZ
      o₂ = addInt (addInt ihead nl) oneZ
      resultTree = Node leftTree (addInt ihead nl) rightTree
  in
  nodeAt sig s (addInt o₂ o₁)
    ≡ nodeAt sig s (addInt ihead n)
  ∧ tree
      sig
      (toFMap sig finalPrev)
      (toFMap sig finalNext)
      s
      root
      resultTree
      ihead
      (addInt ihead n)
  ∧ domainEqual
      (toFMap sig finalPrev)
      (toFMap sig originalPrev)
  ∧ domainEqual
      (toFMap sig finalNext)
      (toFMap sig originalNext)
  ∧ lookupAgreement
      sig
      (toFMap sig finalPrev)
      (toFMap sig originalPrev)
      s
      zeroZ
      ihead
  ∧ lookupAgreement
      sig
      (toFMap sig finalPrev)
      (toFMap sig originalPrev)
      s
      (addInt ihead n)
      (lengthZ s)
  ∧ lookupAgreement
      sig
      (toFMap sig finalNext)
      (toFMap sig originalNext)
      s
      zeroZ
      ihead
  ∧ lookupAgreement
      sig
      (toFMap sig finalNext)
      (toFMap sig originalNext)
      s
      (addInt ihead n)
      (lengthZ s)
  ∧ (zeroZ <Z n → heightBound resultTree n)

rightContinuation :
  (sig : Signature) →
  Store sig →
  Store sig →
  List (Loc sig) →
  Int →
  Int →
  Int →
  Store sig →
  Store sig →
  Tree →
  Set
rightContinuation
  sig originalPrev originalNext s ihead n nl next₁ prev₂ leftTree =
  let middle = nodeAt sig s (addInt ihead nl)
      o₁ = subtractInt (subtractInt n nl) oneZ
      o₂ = addInt (addInt ihead nl) oneZ
      o₃ = contents (toFMap sig next₁) middle
  in
  middle ∈ keys (toFMap sig next₁)
  ∧ (o₃ ≡ contents (toFMap sig next₁) middle →
      ((zeroZ ≤Z n ∧ o₁ <Z n)
       ∧ dll
           sig
           (toFMap sig prev₂)
           (toFMap sig next₁)
           s
           o₃
           o₂
           (addInt o₂ o₁))
      ∧ ((next₂ : Store sig) →
         (prev₃ : Store sig) →
         (temp : Loc sig) →
         (rightTree : Tree) →
         recursivePost
           sig
           prev₂
           next₁
           s
           o₂
           o₁
           next₂
           prev₃
           temp
           rightTree
         →
         middle ∈ keys (toFMap sig next₂)
         ∧ ((next₃ : Store sig) →
            mapUpdatedAt
              (toFMap sig next₃)
              (toFMap sig next₂)
              middle
              temp
            →
            finalRecursiveResult
              sig
              originalPrev
              originalNext
              s
              ihead
              n
              nl
              next₃
              prev₃
              leftTree
              rightTree
              middle)))

leftContinuation :
  (sig : Signature) →
  Store sig →
  Store sig →
  List (Loc sig) →
  Int →
  Int →
  Int →
  Set
leftContinuation sig originalPrev originalNext s ihead n nl =
  let middle = nodeAt sig s (addInt ihead nl)
  in
  (next₁ : Store sig) →
  (prev₁ : Store sig) →
  (leftRoot : Loc sig) →
  (leftTree : Tree) →
  recursivePost
    sig
    originalPrev
    originalNext
    s
    ihead
    nl
    next₁
    prev₁
    leftRoot
    leftTree
  →
  middle ∈ keys (toFMap sig prev₁)
  ∧ ((prev₂ : Store sig) →
     mapUpdatedAt
       (toFMap sig prev₂)
       (toFMap sig prev₁)
       middle
       leftRoot
     →
     rightContinuation
       sig
       originalPrev
       originalNext
       s
       ihead
       n
       nl
       next₁
       prev₂
       leftTree)

zeroBranch :
  (sig : Signature) →
  Store sig →
  Store sig →
  List (Loc sig) →
  Loc sig →
  Int →
  Int →
  Set
zeroBranch sig prev next s head ihead n =
  head ≡ nodeAt sig s (addInt ihead n)
  ∧ tree
      sig
      (toFMap sig prev)
      (toFMap sig next)
      s
      (null sig)
      Empty
      ihead
      (addInt ihead n)
  ∧ domainEqual (toFMap sig prev) (toFMap sig prev)
  ∧ domainEqual (toFMap sig next) (toFMap sig next)
  ∧ (zeroZ <Z n → heightBound Empty n)

nonzeroBranch :
  (sig : Signature) →
  Store sig →
  Store sig →
  List (Loc sig) →
  Loc sig →
  Int →
  Int →
  Set
nonzeroBranch sig prev next s head ihead n =
  let nl = tdivTwo n
  in
  twoZ ≢ zeroZ
  ∧ ((zeroZ ≤Z n ∧ nl <Z n)
     ∧ dll
         sig
         (toFMap sig prev)
         (toFMap sig next)
         s
         head
         ihead
         (addInt ihead nl))
  ∧ leftContinuation sig prev next s ihead n nl

dll-to-bst-rec'vc : Set₁
dll-to-bst-rec'vc =
  (sig : Signature) →
  (prev : Store sig) →
  (next : Store sig) →
  (s : List (Loc sig)) →
  (head : Loc sig) →
  (ihead : Int) →
  (n : Int) →
  dll
    sig
    (toFMap sig prev)
    (toFMap sig next)
    s
    head
    ihead
    (addInt ihead n)
  →
  IfSet
    (intEqual n zeroZ)
    (zeroBranch sig prev next s head ihead n)
    (nonzeroBranch sig prev next s head ihead n)
