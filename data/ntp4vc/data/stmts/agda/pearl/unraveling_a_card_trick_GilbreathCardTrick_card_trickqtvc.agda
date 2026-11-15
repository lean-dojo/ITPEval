-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/unraveling_a_card_trick_GilbreathCardTrick_card_trickqtvc: the full
-- loop verification condition for cutting, reversing, and riffle-shuffling
-- the blocks of the Gilbreath card trick. This file contains no proof.

{-# OPTIONS --safe #-}

module unraveling_a_card_trick_GilbreathCardTrick_card_trickqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _≢_
infixr 5 _++_
infixr 3 _∧_

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

multiplyNatInt : Nat → Int → Int
multiplyNatInt zero y = pos zero
multiplyNatInt (suc n) y = addInt y (multiplyNatInt n y)

multiplyInt : Int → Int → Int
multiplyInt (pos n) y = multiplyNatInt n y
multiplyInt (negsuc n) y = negateInt (multiplyNatInt (suc n) y)

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

lengthNat : {A : Set} → List A → Nat
lengthNat [] = zero
lengthNat (_ ∷ xs) = suc (lengthNat xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (lengthNat xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

nthNat : {A : Set} → Nat → List A → Maybe A
nthNat zero [] = nothing
nthNat zero (x ∷ xs) = just x
nthNat (suc n) [] = nothing
nthNat (suc n) (_ ∷ xs) = nthNat n xs

nthInt : {A : Set} → Int → List A → Maybe A
nthInt (pos n) xs = nthNat n xs
nthInt (negsuc _) xs = nothing

data Shuffle {A : Set} : List A → List A → List A → Set where
  shuffle-nil-left :
    (l : List A) →
    Shuffle l [] l

  shuffle-nil-right :
    (l : List A) →
    Shuffle [] l l

  shuffle-cons-left :
    {a b c : List A} →
    (x : A) →
    Shuffle a b c →
    Shuffle (x ∷ a) b (x ∷ c)

  shuffle-cons-right :
    {a b c : List A} →
    (x : A) →
    Shuffle a b c →
    Shuffle a (x ∷ b) (x ∷ c)

SuitOrdered : Int → Int → List Int → Set
SuitOrdered m n cards =
  (i j : Int) →
  (zeroZ ≤Z i ∧ i <Z n) →
  (zeroZ ≤Z j ∧ j <Z m) →
  nthInt (addInt (multiplyInt i m) j) cards ≡ just j

SuitSorted : Int → Int → List Int → Set
SuitSorted m n cards =
  ((i v : Int) →
    nthInt i cards ≡ just v →
    zeroZ ≤Z v ∧ v <Z m)
  ∧
  ((i j₁ j₂ : Int) →
    (zeroZ ≤Z i ∧ i <Z n) →
    (zeroZ ≤Z j₁ ∧ j₁ <Z m) →
    (zeroZ ≤Z j₂ ∧ j₂ <Z m) →
    nthInt (addInt (multiplyInt i m) j₁) cards ≢
      nthInt (addInt (multiplyInt i m) j₂) cards)

record CardTrickModel : Set₁ where
  field
    m                 : Int
    n                 : Int
    m-positive        : zeroZ <Z m
    n-nonnegative     : zeroZ ≤Z n
    Stack             : Set → Set
    elts              : {A : Set} → Stack A → List A
    gilbreath-card-trick :
      (a : List Int) →
      lengthZ a ≡ multiplyInt n m →
      SuitOrdered m n a →
      (c d : List Int) →
      a ≡ c ++ d →
      (b : List Int) →
      Shuffle c (reverse d) b →
      SuitSorted m n b

open CardTrickModel

stackLength :
  (model : CardTrickModel) →
  {A : Set} →
  Stack model A →
  Int
stackLength model stack = lengthZ (elts model stack)

HeadAndTail :
  (model : CardTrickModel) →
  Stack model Int →
  Int →
  Stack model Int →
  Set
HeadAndTail model a₁ o₁ a₂ with elts model a₁
... | [] = ⊥
... | x ∷ tail = (o₁ ≡ x) ∧ (elts model a₂ ≡ tail)

LoopInvariant :
  (model : CardTrickModel) →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Int →
  Set
LoopInvariant model original d₁ a₁ i =
  stackLength model a₁ ≡
    addInt
      (subtractInt (multiplyInt (n model) (m model)) i)
      oneZ
  ∧
  stackLength model d₁ ≡ subtractInt i oneZ
  ∧
  elts model original ≡ reverse (elts model d₁) ++ elts model a₁

LoopStepConclusion :
  (model : CardTrickModel) →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Int →
  Set
LoopStepConclusion model original d₁ a₁ i =
  elts model a₁ ≢ []
  ∧
  ((a₂ : Stack model Int) →
    (o₁ : Int) →
    HeadAndTail model a₁ o₁ a₂ →
    (d₂ : Stack model Int) →
    elts model d₂ ≡ o₁ ∷ elts model d₁ →
    LoopInvariant model original d₂ a₂ (addInt i oneZ))

ShuffleResult :
  (model : CardTrickModel) →
  List Int →
  List Int →
  Stack model Int →
  Set
ShuffleResult model left right result =
  Shuffle (reverse left) (reverse right) (elts model result) →
  stackLength model result ≡ multiplyInt (n model) (m model)
  ∧ SuitSorted (m model) (n model) (elts model result)

LoopBodyAndExit :
  (model : CardTrickModel) →
  Stack model Int →
  Int →
  Stack model Int →
  Stack model Int →
  Set
LoopBodyAndExit model original cut d₁ a₁ =
  ((i : Int) →
    ((oneZ ≤Z i ∧ i ≤Z cut) ∧
      LoopInvariant model original d₁ a₁ i) →
    LoopStepConclusion model original d₁ a₁ i)
  ∧
  (LoopInvariant model original d₁ a₁ (addInt cut oneZ) →
    ((d₂ a₂ result : Stack model Int) →
      elts model a₂ ≡ [] ∧
      elts model d₂ ≡ [] ∧
      Shuffle
          (reverse (elts model a₁))
          (reverse (elts model d₁))
          (elts model result) →
      stackLength model result ≡ multiplyInt (n model) (m model)
      ∧ SuitSorted (m model) (n model) (elts model result)))

PositiveCutBranch :
  (model : CardTrickModel) →
  Stack model Int →
  Stack model Int →
  Int →
  Set
PositiveCutBranch model original empty cut =
  (stackLength model original ≡
      addInt
        (subtractInt (multiplyInt (n model) (m model)) oneZ)
        oneZ
   ∧ stackLength model empty ≡ subtractInt oneZ oneZ
   ∧ elts model original ≡
      reverse (elts model empty) ++ elts model original)
  ∧
  ((d₁ a₁ : Stack model Int) →
    LoopBodyAndExit model original cut d₁ a₁)

NonpositiveCutBranch :
  (model : CardTrickModel) →
  Stack model Int →
  Stack model Int →
  Set
NonpositiveCutBranch model original empty =
  (d₁ a₁ result : Stack model Int) →
  elts model a₁ ≡ [] ∧
  elts model d₁ ≡ [] ∧
  Shuffle
      (reverse (elts model original))
      (reverse (elts model empty))
      (elts model result) →
  stackLength model result ≡ multiplyInt (n model) (m model)
  ∧ SuitSorted (m model) (n model) (elts model result)

CutObligation :
  (model : CardTrickModel) →
  Stack model Int →
  Stack model Int →
  Int →
  Set
CutObligation model original empty cut =
  (zeroZ ≤Z cut ∧
    cut ≤Z multiplyInt (n model) (m model)) →
  ((oneZ ≤Z addInt cut oneZ →
      PositiveCutBranch model original empty cut)
   ∧
   (addInt cut oneZ <Z oneZ →
      NonpositiveCutBranch model original empty))

CardTrickVC :
  (model : CardTrickModel) →
  Stack model Int →
  Stack model Int →
  Set
CardTrickVC model original empty =
  Exists Int
    (λ result →
      zeroZ ≤Z result ∧
      result ≤Z multiplyInt (n model) (m model))
  ∧
  ((cut : Int) →
    CutObligation model original empty cut)

card-trick'vc : Set₁
card-trick'vc =
  (model : CardTrickModel) →
  (a d′ : Stack model Int) →
  stackLength model a ≡ multiplyInt (n model) (m model) →
  SuitOrdered (m model) (n model) (elts model a) →
  elts model d′ ≡ [] →
  CardTrickVC model a d′
