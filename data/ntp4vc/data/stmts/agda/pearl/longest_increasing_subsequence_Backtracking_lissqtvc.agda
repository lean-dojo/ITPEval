-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/longest_increasing_subsequence_Backtracking_lissqtvc: the
-- backtracking verification condition for constructing a longest strictly
-- increasing subsequence of an abstract totally ordered list. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module longest_increasing_subsequence_Backtracking_lissqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _≤N_
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

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

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

_≤N_ : Nat → Nat → Set
x ≤N y = natLessOrEqual x y ≡ true

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

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

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

record StrictTotalOrder (A : Set) : Set₁ where
  field
    lt : A → A → Set
    transitive :
      (x y z : A) →
      lt x y →
      lt y z →
      lt x z
    asymmetric :
      (x y : A) →
      lt x y →
      Not (lt y x)
    trichotomy :
      (x y : A) →
      lt x y ∨ lt y x ∨ x ≡ y

module LISTheory
  (Elt : Set)
  (eltDefault : Elt)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  (order : StrictTotalOrder Elt)
  where

  open StrictTotalOrder order

  decide : (P : Set) → Dec P
  decide P with excludedMiddle P
  ... | left proof = yes proof
  ... | right refutation = no refutation

  IfDec : {P : Set} → Dec P → Set → Set → Set
  IfDec (yes _) when-true when-false = when-true
  IfDec (no _) when-true when-false = when-false

  IfProp : (P : Set) → Set → Set → Set
  IfProp P when-true when-false =
    IfDec (decide P) when-true when-false

  nthElt : List Elt → Int → Elt
  nthElt xs index =
    nthDefault eltDefault (toNat index) xs

  ISS : List Int → List Elt → Set
  ISS indices word =
    ((i : Int) →
      ((zeroZ ≤Z i) ∧ (i <Z lengthZ indices)) →
      (zeroZ ≤Z nthInt indices i) ∧
      (nthInt indices i <Z lengthZ word)) ∧
    ((i j : Int) →
      ((zeroZ ≤Z i) ∧ (i <Z j) ∧ (j <Z lengthZ indices)) →
      (nthInt indices i <Z nthInt indices j) ∧
      lt
        (nthElt word (nthInt indices i))
        (nthElt word (nthInt indices j)))

  LISS : List Int → List Elt → Set
  LISS indices word =
    ISS indices word ∧
    ((other : List Int) →
      ISS other word →
      length other ≤N length indices)

  MaxTwo :
    List Elt →
    Int →
    Int →
    List Int →
    Set
  MaxTwo word firstIndex upper indices =
    (other : List Int) →
    ISS other word →
    twoZ ≤Z lengthZ other →
    (nthInt other zeroZ ≡ firstIndex) ∧
    (firstIndex <Z nthInt other oneZ) ∧
    (nthInt other oneZ <Z upper) →
    length other ≤N length indices

  MaxOneAt :
    List Elt →
    Int →
    List Int →
    Set
  MaxOneAt word firstIndex indices =
    (other : List Int) →
    ISS other word →
    oneZ ≤Z lengthZ other →
    nthInt other zeroZ ≡ firstIndex →
    length other ≤N length indices

  MaxBefore :
    List Elt →
    Int →
    List Int →
    Set
  MaxBefore word upper indices =
    (other : List Int) →
    ISS other word →
    oneZ ≤Z lengthZ other →
    nthInt other zeroZ <Z upper →
    length other ≤N length indices

  CandidateTwo :
    List Elt →
    Int →
    Int →
    Int →
    List Int →
    Set
  CandidateTwo word expectedLength firstIndex upper indices =
    ((expectedLength ≡ lengthZ indices) ∧
     (zeroZ <Z lengthZ indices)) ∧
    (nthInt indices zeroZ ≡ firstIndex) ∧
    ISS indices word ∧
    MaxTwo word firstIndex upper indices

  CandidateOne :
    List Elt →
    Int →
    Int →
    List Int →
    Set
  CandidateOne word expectedLength firstIndex indices =
    ((expectedLength ≡ lengthZ indices) ∧
     (zeroZ <Z lengthZ indices)) ∧
    (nthInt indices zeroZ ≡ firstIndex) ∧
    ISS indices word ∧
    MaxOneAt word firstIndex indices

  ConsFacts :
    Int →
    List Int →
    List Int →
    Set
  ConsFacts firstIndex tail extended =
    (lengthZ extended ≡ addInt oneZ (lengthZ tail)) ∧
    (nthInt extended zeroZ ≡ firstIndex) ∧
    ((i₁ : Int) →
      ((zeroZ <Z i₁) ∧ (i₁ ≤Z lengthZ tail)) →
      nthInt extended i₁ ≡
        nthInt tail (subtractInt i₁ oneZ))

  ExtendResult :
    List Elt →
    Int →
    Int →
    List Int →
    List Int →
    Set
  ExtendResult word firstIndex upper tail extended =
    ConsFacts firstIndex tail extended →
    CandidateTwo
      word
      (addInt oneZ (lengthZ tail))
      firstIndex
      upper
      extended

  SuccessorResult :
    List Elt →
    Int →
    Int →
    Int →
    List Int →
    List Int →
    Set
  SuccessorResult word firstIndex upper len current successor =
    IfSet
      (intLess len (addInt oneZ (lengthZ successor)))
      (let extended = firstIndex ∷ successor
       in ExtendResult
            word firstIndex upper successor extended)
      (CandidateTwo word len firstIndex upper current)

  SuccessorObligation :
    List Elt →
    Int →
    Int →
    Int →
    List Int →
    List Int →
    Set
  SuccessorObligation word firstIndex successorIndex len current successor =
    ((zeroZ <Z lengthZ successor) ∧
     (nthInt successor zeroZ ≡ successorIndex) ∧
     ISS successor word ∧
     MaxOneAt word successorIndex successor) →
    SuccessorResult
      word firstIndex
      (addInt successorIndex oneZ)
      len current successor

  OrderedBranch :
    List Elt →
    Int →
    Int →
    Int →
    List Int →
    Set
  OrderedBranch word firstIndex successorIndex len current =
    (((zeroZ ≤Z subtractInt (lengthZ word) firstIndex) ∧
      (subtractInt (lengthZ word) successorIndex
        <Z subtractInt (lengthZ word) firstIndex)) ∧
     (zeroZ ≤Z successorIndex) ∧
     (successorIndex <Z lengthZ word)) ∧
    ((successor : List Int) →
      SuccessorObligation
        word firstIndex successorIndex len current successor)

  InnerStep :
    List Elt →
    Int →
    Int →
    Int →
    List Int →
    Int →
    Set
  InnerStep word firstIndex successorIndex len current nextUpper =
    IfProp
      (lt
        (nthElt word firstIndex)
        (nthElt word successorIndex))
      (OrderedBranch
        word firstIndex successorIndex len current)
      (CandidateTwo
        word len firstIndex nextUpper current)

  InnerState :
    List Elt →
    Int →
    Int →
    Int →
    Int →
    List Int →
    Int →
    Set
  InnerState word firstIndex lower upper successorIndex current len =
    ((lower ≤Z successorIndex) ∧
     (successorIndex ≤Z upper)) ∧
    CandidateTwo
      word len firstIndex successorIndex current

  InnerLoop :
    List Elt →
    Int →
    Int →
    Int →
    List Int →
    Int →
    Set
  InnerLoop word firstIndex lower upper current len =
    (((successorIndex : Int) →
      InnerState
        word firstIndex lower upper successorIndex current len →
      InnerStep
        word firstIndex successorIndex len current
        (addInt successorIndex oneZ)) ∧
     (CandidateTwo
        word len firstIndex (addInt upper oneZ) current →
      CandidateOne word len firstIndex current))

  NonemptyInnerRange :
    List Elt →
    Int →
    Int →
    Int →
    List Int →
    Set
  NonemptyInnerRange word firstIndex lower upper singleton =
    CandidateTwo
      word oneZ firstIndex lower singleton ∧
    ((current : List Int) →
      (len : Int) →
      InnerLoop word firstIndex lower upper current len)

  BacktrackFrom :
    List Elt →
    Int →
    List Int →
    Set
  BacktrackFrom word firstIndex singleton =
    let last = subtractInt (lengthZ word) oneZ
        lower = addInt firstIndex oneZ
    in
    ((lower ≤Z addInt last oneZ) →
      NonemptyInnerRange
        word firstIndex lower last singleton) ∧
    ((addInt last oneZ <Z lower) →
      CandidateOne word oneZ firstIndex singleton)

  SingletonObligation :
    List Elt →
    Int →
    List Int →
    Set
  SingletonObligation word firstIndex singleton =
    ((lengthZ singleton ≡ oneZ) ∧
     (nthInt singleton zeroZ ≡ firstIndex)) →
    BacktrackFrom word firstIndex singleton

  PerStartingIndex : List Elt → Set
  PerStartingIndex word =
    (firstIndex : Int) →
    ((zeroZ ≤Z firstIndex) ∧
     (firstIndex <Z lengthZ word)) →
    let singleton = firstIndex ∷ []
    in SingletonObligation word firstIndex singleton

  PrefixState :
    List Elt →
    Int →
    Int →
    List Int →
    Set
  PrefixState word len upper current =
    (len ≡ lengthZ current) ∧
    ISS current word ∧
    MaxBefore word upper current

  StartingCandidateResult :
    List Elt →
    Int →
    Int →
    List Int →
    List Int →
    Set
  StartingCandidateResult word index len current candidate =
    IfSet
      (intLess len (lengthZ candidate))
      (ISS candidate word ∧
       MaxBefore word (addInt index oneZ) candidate)
      ((len ≡ lengthZ current) ∧
       ISS current word ∧
       MaxBefore word (addInt index oneZ) current)

  StartingCandidateObligation :
    List Elt →
    Int →
    Int →
    List Int →
    List Int →
    Set
  StartingCandidateObligation word index len current candidate =
    ((zeroZ <Z lengthZ candidate) ∧
     (nthInt candidate zeroZ ≡ index) ∧
     ISS candidate word ∧
     MaxOneAt word index candidate) →
    StartingCandidateResult word index len current candidate

  OuterStep :
    List Elt →
    Int →
    Int →
    List Int →
    Int →
    Set
  OuterStep word last len current index =
    (((zeroZ ≤Z index) ∧ (index ≤Z last)) ∧
     PrefixState word len index current) →
    ((zeroZ ≤Z index) ∧ (index <Z lengthZ word)) ∧
    ((candidate : List Int) →
      StartingCandidateObligation
        word index len current candidate)

  OuterLoop :
    List Elt →
    Int →
    List Int →
    Int →
    Set
  OuterLoop word last current len =
    (((index : Int) →
      OuterStep word last len current index) ∧
     (PrefixState
        word len (addInt last oneZ) current →
      (len ≡ lengthZ current) ∧
      LISS current word))

  NonemptyOuterRange :
    List Elt →
    Int →
    Set
  NonemptyOuterRange word last =
    ((zeroZ ≡ lengthZ ([] {A = Int})) ∧
     ISS [] word ∧
     MaxBefore word zeroZ []) ∧
    ((current : List Int) →
      (len : Int) →
      OuterLoop word last current len)

  CompleteSearch : List Elt → Set
  CompleteSearch word =
    let last = subtractInt (lengthZ word) oneZ
    in
    ((zeroZ ≤Z addInt last oneZ) →
      NonemptyOuterRange word last) ∧
    ((addInt last oneZ <Z zeroZ) →
      (zeroZ ≡ lengthZ ([] {A = Int})) ∧
      LISS [] word)

  liss-vc : (word : List Elt) → Set
  liss-vc word =
    PerStartingIndex word ∧
    CompleteSearch word
