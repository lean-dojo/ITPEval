-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/patience_PatienceAbstract_play_cardsqtvc: the verification condition
-- for recursively adding a list of integer-valued cards to an abstract
-- patience-solitaire state while preserving its invariant and value history.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module patience_PatienceAbstract_play_cardsqtvc where

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

data ⊥ : Set where

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

FunctionEqual : {A B : Set} → (A → B) → (A → B) → Set
FunctionEqual f g = (x : _) → f x ≡ g x

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

TailMatches : List Int → List Int → Set
TailMatches [] rem = ⊥
TailMatches (_ ∷ tail) rem = tail ≡ rem

StateAfterOneCard : State → State → Int → Set
StateAfterOneCard s s₁ c =
  Inv s₁
  ∧ numElts s₁ ≡ addInt (numElts s) oneZ
  ∧ FunctionEqual
      (values s₁)
      (updateInt (values s) (numElts s) c)

StateAfterRemainder : State → State → List Int → Set
StateAfterRemainder s₁ s₂ rem =
  Inv s₂
  ∧ numElts s₂ ≡ addInt (numElts s₁) (lengthZ rem)
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z numElts s₁) →
    values s₂ i ≡ values s₁ i)
  ∧
  ((i : Int) →
    (numElts s₁ ≤Z i ∧ i <Z numElts s₂) →
    values s₂ i ≡
      nthInt rem (subtractInt i (numElts s₁)))

FinalState : State → State → List Int → Set
FinalState s s₂ input =
  Inv s₂
  ∧ numElts s₂ ≡ addInt (numElts s) (lengthZ input)
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z numElts s) →
    values s₂ i ≡ values s i)
  ∧
  ((i : Int) →
    (numElts s ≤Z i ∧ i <Z numElts s₂) →
    values s₂ i ≡
      nthInt input (subtractInt i (numElts s)))

PlayCardsCase : State → List Int → Set
PlayCardsCase s [] =
  Inv s
  ∧ numElts s ≡ addInt (numElts s) (lengthZ {A = Int} [])
  ∧
  ((i : Int) →
    (numElts s ≤Z i ∧ i <Z numElts s) →
    values s i ≡ nthInt [] (subtractInt i (numElts s)))
PlayCardsCase s (c ∷ rem) =
  Inv s
  ∧
  ((s₁ : State) →
    StateAfterOneCard s s₁ c →
    (TailMatches (c ∷ rem) rem ∧ Inv s₁)
    ∧
    ((s₂ : State) →
      StateAfterRemainder s₁ s₂ rem →
      FinalState s s₂ (c ∷ rem)))

play-cards'vc : Set
play-cards'vc =
  (s : State) →
  (input : List Int) →
  Inv s →
  PlayCardsCase s input
