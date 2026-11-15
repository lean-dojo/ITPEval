-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/patience_PatienceAbstract_play_gameqtvc: the verification condition
-- for an abstract patience-solitaire game, including construction of a
-- longest strictly increasing subsequence from the final stack state.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module patience_PatienceAbstract_play_gameqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 4 _×_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

zeroZ oneZ minusOneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
minusOneZ = negsuc zero

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

constant : {A B : Set} → A → B → A
constant value _ = value

updateInt : (Int → Int) → Int → Int → Int → Int
updateInt old key value query with intEqual query key
... | true = value
... | false = old query

record State : Set where
  constructor state
  field
    numStacks  : Int
    numElts    : Int
    values     : Int → Int
    stackSizes : Int → Int
    stacks     : Int → Int → Int
    positions  : Int → Int × Int
    preds      : Int → Int

open State public

stackOf : State → Int → Int
stackOf s i = fst (positions s i)

heightOf : State → Int → Int
heightOf s i = snd (positions s i)

Inv : State → Set
Inv s =
  (zeroZ ≤Z numStacks s ∧ numStacks s ≤Z numElts s)
  ∧
  (zeroZ <Z numElts s → zeroZ <Z numStacks s)
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z numStacks s) →
    oneZ ≤Z stackSizes s i
    ∧
    ((j : Int) →
      (zeroZ ≤Z j ∧ j <Z stackSizes s i) →
      zeroZ ≤Z stacks s i j
      ∧ stacks s i j <Z numElts s))
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z numElts s) →
    (zeroZ ≤Z stackOf s i ∧ stackOf s i <Z numStacks s)
    ∧
    (zeroZ ≤Z heightOf s i
     ∧ heightOf s i <Z stackSizes s (stackOf s i)
     ∧ stacks s (stackOf s i) (heightOf s i) ≡ i))
  ∧
  ((is : Int) →
    (zeroZ ≤Z is ∧ is <Z numStacks s) →
    (ip : Int) →
    (zeroZ ≤Z ip ∧ ip <Z stackSizes s is) →
    (is , ip) ≡ positions s (stacks s is ip))
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z numStacks s) →
    (j k : Int) →
    (zeroZ ≤Z j ∧ j <Z k ∧ k <Z stackSizes s i) →
    stacks s i j <Z stacks s i k)
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z numStacks s) →
    (j k : Int) →
    (zeroZ ≤Z j ∧ j ≤Z k ∧ k <Z stackSizes s i) →
    values s (stacks s i k) ≤Z values s (stacks s i j))
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z numElts s) →
    let pred = preds s i
    in
    (minusOneZ ≤Z pred ∧ pred <Z numElts s)
    ∧
    pred <Z i
    ∧
    IfSet
      (intLess pred zeroZ)
      (stackOf s i ≡ zeroZ)
      (values s pred <Z values s i
       ∧ zeroZ <Z stackOf s i
       ∧ stackOf s pred ≡ subtractInt (stackOf s i) oneZ))

record Seq (A : Set) : Set where
  constructor seq
  field
    seqLen : Int
    seqVal : Int → A

open Seq public

IncreasingSubsequence : Seq Int → List Int → Set
IncreasingSubsequence sigma input =
  (zeroZ ≤Z seqLen sigma ∧ seqLen sigma ≤Z lengthZ input)
  ∧
  (((i : Int) →
      (zeroZ ≤Z i ∧ i <Z seqLen sigma) →
      zeroZ ≤Z seqVal sigma i
      ∧ seqVal sigma i <Z lengthZ input)
   ∧
   ((i j : Int) →
      (zeroZ ≤Z i ∧ i <Z j ∧ j <Z seqLen sigma) →
      seqVal sigma i <Z seqVal sigma j))
  ∧
  ((i j : Int) →
    (zeroZ ≤Z i ∧ i <Z j ∧ j <Z seqLen sigma) →
    nthInt input (seqVal sigma i)
      <Z nthInt input (seqVal sigma j))

MaximalIncreasingSubsequence : State → List Int → Set
MaximalIncreasingSubsequence s input =
  Exists
    (Seq Int)
    (λ sigma →
      seqLen sigma ≡ numStacks s
      ∧ IncreasingSubsequence sigma input)
  ∧
  ((sigma : Seq Int) →
    IncreasingSubsequence sigma input →
    seqLen sigma ≤Z numStacks s)

LoopInvariant :
  State →
  Int →
  Int →
  (Int → Int) →
  Int →
  Set
LoopInvariant s ns i sequence index =
  (minusOneZ ≤Z index ∧ index <Z numElts s)
  ∧
  (zeroZ ≤Z i →
    zeroZ ≤Z index
    ∧ stackOf s index ≡ i)
  ∧
  (addInt i oneZ <Z ns →
    index <Z sequence (addInt i oneZ))
  ∧
  ((zeroZ ≤Z i ∧ i <Z subtractInt ns oneZ) →
    values s index <Z values s (sequence (addInt i oneZ)))
  ∧
  ((j : Int) →
    (i <Z j ∧ j <Z ns) →
    zeroZ ≤Z sequence j
    ∧ sequence j <Z numElts s)
  ∧
  ((j k : Int) →
    (i <Z j ∧ j <Z k ∧ k <Z ns) →
    sequence j <Z sequence k)
  ∧
  ((j k : Int) →
    (i <Z j ∧ j <Z k ∧ k <Z ns) →
    values s (sequence j) <Z values s (sequence k))

LoopPreservation :
  State →
  Int →
  Int →
  (Int → Int) →
  Int →
  Set
LoopPreservation s ns upper sequence index =
  (i : Int) →
  (i ≤Z upper ∧ zeroZ ≤Z i)
  ∧ LoopInvariant s ns i sequence index →
  LoopInvariant
    s
    ns
    (subtractInt i oneZ)
    (updateInt sequence i index)
    (preds s index)

LoopObligations : State → List Int → Int → Int → Set
LoopObligations s input ns upper =
  (sequence : Int → Int) →
  (index : Int) →
  LoopPreservation s ns upper sequence index
  ∧
  (LoopInvariant s ns (subtractInt zeroZ oneZ) sequence index →
    MaximalIncreasingSubsequence s input)

NonemptyBranch : State → List Int → Set
NonemptyBranch s input =
  let ns = numStacks s
      topIndex =
        stacks s
          (subtractInt ns oneZ)
          (subtractInt
            (stackSizes s (subtractInt ns oneZ))
            oneZ)
      emptySequence = constant {A = Int} {B = Int} minusOneZ
      upper = subtractInt ns oneZ
      loopStart = subtractInt zeroZ oneZ
  in
  (loopStart ≤Z upper →
    LoopInvariant s ns upper emptySequence topIndex
    ∧ LoopObligations s input ns upper)
  ∧
  (upper <Z loopStart →
    MaximalIncreasingSubsequence s input)

FinalStateObligation : List Int → State → Set
FinalStateObligation input s =
  Inv s
  ∧ numElts s ≡ addInt zeroZ (lengthZ input)
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z zeroZ) →
    values s i ≡ constant {A = Int} {B = Int} minusOneZ i)
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z numElts s) →
    values s i ≡ nthInt input (subtractInt i zeroZ))

initialState : State
initialState =
  state
    zeroZ
    zeroZ
    (constant {A = Int} {B = Int} minusOneZ)
    (constant {A = Int} {B = Int} zeroZ)
    (constant
      {A = Int → Int}
      {B = Int}
      (constant {A = Int} {B = Int} minusOneZ))
    (constant {A = Int × Int} {B = Int} (minusOneZ , minusOneZ))
    (constant {A = Int} {B = Int} minusOneZ)

play-game'vc : List Int → Set
play-game'vc input =
  Inv initialState
  ∧
  ((s : State) →
    FinalStateObligation input s →
    IfSet
      (intEqual (numStacks s) zeroZ)
      (MaximalIncreasingSubsequence s input)
      (NonemptyBranch s input))
