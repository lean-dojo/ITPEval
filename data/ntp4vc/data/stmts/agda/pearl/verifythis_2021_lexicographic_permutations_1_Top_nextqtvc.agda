-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_lexicographic_permutations_1_Top_nextqtvc: the
-- verification condition for the in-place lexicographic next-permutation
-- algorithm, including both search loops, swaps, suffix reversal, and the
-- absence of an intermediate permutation. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021LexicographicPermutations1TopNextVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _≢_
infixr 3 _∧_
infixr 2 _∨_

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
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

zeroZ oneZ minusOneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
minusOneZ = negsuc zero

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

Bounds : Int → List Int → Set
Bounds index xs =
  zeroZ ≤Z index ∧ index <Z lengthZ xs

countInt : Int → List Int → Nat
countInt value [] = zero
countInt value (x ∷ xs) with intEqual value x
... | true = suc (countInt value xs)
... | false = countInt value xs

occAll : Int → List Int → Int
occAll value xs = pos (countInt value xs)

record SequenceModel : Set where
  field
    toSeq : List Int → List Int
    toSeq-length :
      (a : List Int) →
      length (toSeq a) ≡ length a
    toSeq-index :
      (a : List Int) →
      (i : Int) →
      zeroZ ≤Z i →
      i <Z lengthZ (toSeq a) →
      nthInt (toSeq a) i ≡ nthInt a i

open SequenceModel

IsPermutationOf :
  SequenceModel → List Int → List Int → Set
IsPermutationOf model p a =
  length p ≡ length a
  ∧ ((x : Int) → occAll x p ≡ occAll x a)

LexLess : List Int → List Int → Set
LexLess p q =
  (length p ≡ length q ∧ zeroZ <Z lengthZ q)
  ∧ Exists Int
      (λ i →
        (zeroZ ≤Z i ∧ i <Z lengthZ p)
        ∧ ((j : Int) →
            (zeroZ ≤Z j ∧ j <Z i) →
            nthInt p j ≡ nthInt q j)
        ∧ nthInt p i <Z nthInt q i)

Descending : List Int → Int → Int → Set
Descending s lo hi =
  (zeroZ ≤Z lo ∧ lo ≤Z hi ∧ hi ≤Z lengthZ s)
  ∧ ((i j : Int) →
      (lo ≤Z i ∧ i ≤Z j ∧ j <Z hi) →
      nthInt s j ≤Z nthInt s i)

WhileInvariant :
  SequenceModel → List Int → Int → Int → Set
WhileInvariant model a n i =
  (minusOneZ ≤Z i ∧ i <Z n)
  ∧
  ((i ≡ minusOneZ ∧ n ≡ zeroZ)
   ∨
   (zeroZ ≤Z i ∧ Descending (toSeq model a) i n))

UnchangedExcept :
  List Int → List Int → Int → Int → Set
UnchangedExcept newer older left-index right-index =
  (k : Int) →
  Bounds k newer →
  k ≢ left-index →
  k ≢ right-index →
  nthInt newer k ≡ nthInt older k

SwapContract :
  SequenceModel →
  List Int → List Int → Int → Int → Set
SwapContract model newer older left-index right-index =
  nthInt newer left-index ≡ nthInt older right-index
  ∧ nthInt newer right-index ≡ nthInt older left-index
  ∧ UnchangedExcept newer older left-index right-index
  ∧ IsPermutationOf model
      (toSeq model newer)
      (toSeq model older)

CopyBefore : List Int → List Int → Int → Set
CopyBefore newer original upper =
  (k : Int) →
  (zeroZ ≤Z k ∧ k <Z upper) →
  nthInt newer k ≡ nthInt original k

MirrorInitial :
  List Int → Int → Int → Int → Set
MirrorInitial a1 i0 i n =
  (k : Int) →
  (zeroZ <Z k ∧ k <Z subtractInt i i0) →
  nthInt a1 (addInt i0 k) ≡
    nthInt a1 (subtractInt n k)
  ∧ nthInt a1 (subtractInt n k) ≡
    nthInt a1 (addInt i0 k)

MirrorLoop :
  List Int → List Int → Int → Int → Int → Set
MirrorLoop current at-loop i0 i1 n =
  (k : Int) →
  (zeroZ <Z k ∧ k <Z subtractInt i1 i0) →
  nthInt current (addInt i0 k) ≡
    nthInt at-loop (subtractInt n k)
  ∧ nthInt current (subtractInt n k) ≡
    nthInt at-loop (addInt i0 k)

MiddleUnchanged :
  List Int → List Int → Int → Int → Set
MiddleUnchanged current at-loop lower upper =
  (k : Int) →
  (lower ≤Z k ∧ k ≤Z upper) →
  nthInt current k ≡ nthInt at-loop k

ReverseInvariant :
  SequenceModel →
  List Int → List Int → List Int →
  Int → Int → Int → Int → Int → List Int → Set
ReverseInvariant model original a0 a1 i0 z n j1 i1 a2 =
  (i0 <Z i1 ∧ i0 <Z j1 ∧ j1 <Z n)
  ∧ IsPermutationOf model (toSeq model a2) a0
  ∧ CopyBefore a2 original i0
  ∧ nthInt a2 i0 ≡ z
  ∧ subtractInt i1 i0 ≡ subtractInt n j1
  ∧ MiddleUnchanged a2 a1 i1 j1
  ∧ MirrorLoop a2 a1 i0 i1 n

ReverseAfterStep :
  SequenceModel →
  List Int → List Int → List Int → List Int →
  Int → Int → Int → Int → Int → Set
ReverseAfterStep model original a0 a1 a3 i0 z n j1 i1 =
  (zeroZ ≤Z subtractInt j1 i1
   ∧ subtractInt
       (subtractInt j1 oneZ)
       (addInt i1 oneZ)
     <Z subtractInt j1 i1)
  ∧
  (i0 <Z addInt i1 oneZ
   ∧ i0 <Z subtractInt j1 oneZ
   ∧ subtractInt j1 oneZ <Z n)
  ∧ IsPermutationOf model (toSeq model a3) a0
  ∧ CopyBefore a3 original i0
  ∧ nthInt a3 i0 ≡ z
  ∧ subtractInt (addInt i1 oneZ) i0 ≡
      subtractInt n (subtractInt j1 oneZ)
  ∧ MiddleUnchanged
      a3 a1
      (addInt i1 oneZ)
      (subtractInt j1 oneZ)
  ∧ MirrorLoop a3 a1 i0 (addInt i1 oneZ) n

PrefixEqual :
  List Int → List Int → Int → Int → Set
PrefixEqual p reference lower upper =
  (k : Int) →
  (lower ≤Z k ∧ k <Z upper) →
  nthInt p k ≡ nthInt reference k

ScanContradiction :
  List Int → List Int → Int → Int → Int → Set
ScanContradiction p reference i0 o6 o7 =
  o7 ≤Z addInt o6 oneZ →
  PrefixEqual p reference (addInt i0 oneZ) o7
  ∧
  ((l : Int) →
    ((o7 ≤Z l ∧ l ≤Z o6)
     ∧ PrefixEqual p reference (addInt i0 oneZ) l) →
    nthInt p l ≡ nthInt reference l
    ∧ PrefixEqual
        p reference
        (addInt i0 oneZ)
        (addInt l oneZ))
  ∧ Not
      (PrefixEqual
        p reference
        (addInt i0 oneZ)
        (addInt o6 oneZ))
  ∧ Not (addInt o6 oneZ <Z o7)

SequenceCopySpec : List Int → List Int → Set
SequenceCopySpec sequence array =
  length sequence ≡ length array
  ∧ ((i : Int) →
      Bounds i sequence →
      nthInt sequence i ≡ nthInt array i)

Between :
  SequenceModel →
  List Int → List Int → List Int → List Int → Set
Between model original a0 current p =
  IsPermutationOf model p a0
  ∧ LexLess (toSeq model original) p
  ∧ LexLess p (toSeq model current)

LemmaBranch :
  SequenceModel →
  List Int → List Int → List Int →
  Int → Int → Int → Int → List Int → Set
LemmaBranch model original a0 current i0 x z n p =
  let a11 = toSeq model original
      v = nthInt p i0
      o6 = subtractInt n oneZ
      o7 = addInt i0 oneZ
  in
  IfSet
    (intEqual v x)
    (ScanContradiction p a11 i0 o6 o7)
    (v ≡ z
     ∧
     (let a21 = toSeq model current
      in
      SequenceCopySpec a21 current →
      ScanContradiction p a21 i0 o6 o7))

SuccessorResult :
  SequenceModel →
  List Int → List Int → List Int → Set
SuccessorResult model original a0 current =
  IsPermutationOf model (toSeq model current) a0
  ∧ LexLess (toSeq model original) (toSeq model current)
  ∧ ((p : List Int) →
      IsPermutationOf model p a0 →
      Not
        (LexLess (toSeq model original) p
         ∧ LexLess p (toSeq model current)))

ReverseLoopExit :
  SequenceModel →
  List Int → List Int → List Int →
  Int → Int → Int → Int → Set
ReverseLoopExit model original a0 current i0 x z n =
  ((p : List Int) →
    Between model original a0 current p →
    LemmaBranch model original a0 current i0 x z n p)
  ∧
  (((p : List Int) →
      Not (Between model original a0 current p)) →
    SuccessorResult model original a0 current)

ReverseLoopStep :
  SequenceModel →
  List Int → List Int → List Int → List Int →
  Int → Int → Int → Int → Int → Int → Set
ReverseLoopStep model original a0 a1 a2 i0 x z n j1 i1 =
  IfSet
    (intLess i1 j1)
    ((Bounds i1 a2 ∧ Bounds j1 a2)
     ∧
     ((a3 : List Int) →
      length a3 ≡ length a2 →
      SwapContract model a3 a2 i1 j1 →
      ReverseAfterStep
        model original a0 a1 a3 i0 z n j1 i1))
    (ReverseLoopExit model original a0 a2 i0 x z n)

ReverseLoopObligations :
  SequenceModel →
  List Int → List Int → List Int →
  Int → Int → Int → Int → Set
ReverseLoopObligations model original a0 a1 i0 x z n =
  (j1 i1 : Int) →
  (a2 : List Int) →
  length a2 ≡ length a1 →
  ReverseInvariant model original a0 a1 i0 z n j1 i1 a2 →
  ReverseLoopStep model original a0 a1 a2 i0 x z n j1 i1

InitialReverseState :
  SequenceModel →
  List Int → List Int → List Int →
  Int → Int → Int → Int → Set
InitialReverseState model original a0 a1 i0 z n i =
  (i0 <Z i
   ∧ i0 <Z subtractInt n oneZ
   ∧ subtractInt n oneZ <Z n)
  ∧ IsPermutationOf model (toSeq model a1) a0
  ∧ CopyBefore a1 original i0
  ∧ nthInt a1 i0 ≡ z
  ∧ subtractInt i i0 ≡
      subtractInt n (subtractInt n oneZ)
  ∧ MirrorInitial a1 i0 i n

AfterFirstSwap :
  SequenceModel →
  List Int → List Int →
  Int → Int → Int → Int → Int → Set
AfterFirstSwap model original a0 n i i0 x j =
  let z = nthInt original j
      o5 = subtractInt i oneZ
  in
  (Bounds o5 original ∧ Bounds j original)
  ∧
  ((a1 : List Int) →
    length a1 ≡ length original →
    SwapContract model a1 original o5 j →
    InitialReverseState model original a0 a1 i0 z n i
    ∧ ReverseLoopObligations
        model original a0 a1 i0 x z n)

SearchJBody :
  SequenceModel →
  List Int → List Int →
  Int → Int → Int → Int → Int → Set
SearchJBody model original a0 n i i0 x j =
  let o4 = subtractInt i oneZ
  in
  Bounds o4 original
  ∧ Bounds j original
  ∧
  IfSet
    (intLessOrEqual (nthInt original j) (nthInt original o4))
    ((zeroZ ≤Z j ∧ subtractInt j oneZ <Z j)
     ∧ (i ≤Z subtractInt j oneZ
        ∧ subtractInt j oneZ <Z n)
     ∧ ((k : Int) →
         (subtractInt j oneZ <Z k ∧ k <Z n) →
         nthInt original k ≤Z x))
    (Bounds j original
     ∧ AfterFirstSwap model original a0 n i i0 x j)

SearchJ :
  SequenceModel →
  List Int → List Int →
  Int → Int → Int → Int → Int → Set
SearchJ model original a0 n i i0 x o3 =
  ((i ≤Z o3 ∧ o3 <Z n)
   ∧ ((k : Int) →
       (o3 <Z k ∧ k <Z n) →
       nthInt original k ≤Z x))
  ∧
  ((j : Int) →
    ((i ≤Z j ∧ j <Z n)
     ∧ ((k : Int) →
         (j <Z k ∧ k <Z n) →
         nthInt original k ≤Z x)) →
    SearchJBody model original a0 n i i0 x j)

PositiveCase :
  SequenceModel →
  List Int → List Int → Int → Int → Set
PositiveCase model original a0 n i =
  let i0 = subtractInt i oneZ
      x = nthInt original i0
      o3 = subtractInt n oneZ
  in
  Bounds i0 original
  ∧ SearchJ model original a0 n i i0 x o3

NoSuccessor :
  SequenceModel → List Int → List Int → Set
NoSuccessor model original a0 =
  IsPermutationOf model (toSeq model original) a0
  ∧ ((p : List Int) →
      IsPermutationOf model p a0 →
      Not (LexLess (toSeq model original) p))

LoopConditionTrue :
  SequenceModel → List Int → Int → Int → Set
LoopConditionTrue model original n i =
  (zeroZ ≤Z i ∧ subtractInt i oneZ <Z i)
  ∧ (minusOneZ ≤Z subtractInt i oneZ
     ∧ subtractInt i oneZ <Z n)
  ∧
  ((subtractInt i oneZ ≡ minusOneZ ∧ n ≡ zeroZ)
   ∨
   (zeroZ ≤Z subtractInt i oneZ
    ∧ Descending
        (toSeq model original)
        (subtractInt i oneZ)
        n))

LoopBody :
  SequenceModel →
  List Int → List Int → Int → Int → Set
LoopBody model original a0 n i =
  (zeroZ <Z i →
    Bounds i original
    ∧ Bounds (subtractInt i oneZ) original)
  ∧
  ((condition : Bool) →
    condition ≡
      ifValue
        (intLess zeroZ i)
        (intLessOrEqual
          (nthInt original i)
          (nthInt original (subtractInt i oneZ)))
        false →
    IfSet
      condition
      (LoopConditionTrue model original n i)
      (IfSet
        (intLessOrEqual i zeroZ)
        (NoSuccessor model original a0)
        (PositiveCase model original a0 n i)))

NextVC :
  SequenceModel → List Int → List Int → Set
NextVC model a a0 =
  length a ≡ length a0 →
  IsPermutationOf model (toSeq model a) a0 →
  let n = lengthZ a
      o1 = subtractInt n oneZ
  in
  WhileInvariant model a n o1
  ∧ ((i : Int) →
      WhileInvariant model a n i →
      LoopBody model a a0 n i)

next'vc : Set
next'vc =
  (model : SequenceModel) →
  (a a0 : List Int) →
  NextVC model a a0
