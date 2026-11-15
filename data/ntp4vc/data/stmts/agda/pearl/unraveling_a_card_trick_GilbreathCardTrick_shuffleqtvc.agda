-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/unraveling_a_card_trick_GilbreathCardTrick_shuffleqtvc: the loop
-- verification condition for building a riffle shuffle from two stacks.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module unraveling_a_card_trick_GilbreathCardTrick_shuffleqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
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

If : Bool → Set → Set → Set
If true then-branch else-branch = then-branch
If false then-branch else-branch = else-branch

ifBool : Bool → Bool → Bool → Bool
ifBool true then-branch else-branch = then-branch
ifBool false then-branch else-branch = else-branch

notBool : Bool → Bool
notBool true = false
notBool false = true

isEmpty : {A : Set} → List A → Bool
isEmpty [] = true
isEmpty (_ ∷ _) = false

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

zeroZ : Int
zeroZ = pos zero

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

record StackModel : Set₁ where
  field
    Stack : Set → Set
    elts  : {A : Set} → Stack A → List A

open StackModel

stackLength :
  (model : StackModel) →
  {A : Set} →
  Stack model A →
  Int
stackLength model stack = lengthZ (elts model stack)

HeadIs : List Int → Int → Set
HeadIs [] value = ⊥
HeadIs (x ∷ xs) value = value ≡ x

HeadAndTail :
  (model : StackModel) →
  Stack model Int →
  Int →
  Stack model Int →
  Set
HeadAndTail model stack value tail-stack with elts model stack
... | [] = ⊥
... | x ∷ xs =
  value ≡ x ∧ elts model tail-stack ≡ xs

ChoiceForFirstTest :
  (model : StackModel) →
  Stack model Int →
  Stack model Int →
  Bool →
  Set
ChoiceForFirstTest model a₁ b₁ choice =
  If
    (isEmpty (elts model a₁))
    (choice ≡ ifBool (isEmpty (elts model b₁)) true false)
    (choice ≡ false)

ChoiceForSecondTest :
  (model : StackModel) →
  Stack model Int →
  Stack model Int →
  Bool →
  Set
ChoiceForSecondTest model a₁ b₁ choice =
  If
    (notBool (isEmpty (elts model a₁)))
    (elts model b₁ ≡ [] → choice ≡ true)
    (choice ≡ false)

LeftStep :
  (model : StackModel) →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Set
LeftStep model original-a original-b a′₁ b′₁ c₁ a₁ b₁ =
  elts model a₁ ≢ []
  ∧
  ((head : Int) →
    HeadIs (elts model a₁) head →
    (a′₂ : Stack model Int) →
    elts model a′₂ ≡ head ∷ elts model a′₁ →
    elts model a₁ ≢ []
    ∧
    ((a₂ : Stack model Int) →
      (popped : Int) →
      HeadAndTail model a₁ popped a₂ →
      (c₂ : Stack model Int) →
      elts model c₂ ≡ popped ∷ elts model c₁ →
      (zeroZ ≤Z
        addInt (stackLength model a₁) (stackLength model b₁)
       ∧
       addInt (stackLength model a₂) (stackLength model b₁) <Z
        addInt (stackLength model a₁) (stackLength model b₁))
      ∧
      reverse (elts model original-a) ≡
        reverse (elts model a₂) ++ elts model a′₂
      ∧
      reverse (elts model original-b) ≡
        reverse (elts model b₁) ++ elts model b′₁
      ∧
      Shuffle
        (elts model a′₂)
        (elts model b′₁)
        (elts model c₂)))

RightStep :
  (model : StackModel) →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Set
RightStep model original-a original-b a′₁ b′₁ c₁ a₁ b₁ =
  elts model b₁ ≢ []
  ∧
  ((head : Int) →
    HeadIs (elts model b₁) head →
    (b′₂ : Stack model Int) →
    elts model b′₂ ≡ head ∷ elts model b′₁ →
    elts model b₁ ≢ []
    ∧
    ((b₂ : Stack model Int) →
      (popped : Int) →
      HeadAndTail model b₁ popped b₂ →
      (c₂ : Stack model Int) →
      elts model c₂ ≡ popped ∷ elts model c₁ →
      (zeroZ ≤Z
        addInt (stackLength model a₁) (stackLength model b₁)
       ∧
       addInt (stackLength model a₁) (stackLength model b₂) <Z
        addInt (stackLength model a₁) (stackLength model b₁))
      ∧
      reverse (elts model original-a) ≡
        reverse (elts model a₁) ++ elts model a′₁
      ∧
      reverse (elts model original-b) ≡
        reverse (elts model b₂) ++ elts model b′₂
      ∧
      Shuffle
        (elts model a′₁)
        (elts model b′₂)
        (elts model c₂)))

LoopContinuation :
  (model : StackModel) →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Bool →
  Set
LoopContinuation
  model original-a original-b a′₁ b′₁ c₁ a₁ b₁ first-choice =
  If
    (notBool first-choice)
    ((second-choice : Bool) →
      ChoiceForSecondTest model a₁ b₁ second-choice →
      If
        second-choice
        (LeftStep
          model original-a original-b a′₁ b′₁ c₁ a₁ b₁)
        (RightStep
          model original-a original-b a′₁ b′₁ c₁ a₁ b₁))
    (elts model a₁ ≡ []
     ∧ elts model b₁ ≡ []
     ∧ Shuffle
        (reverse (elts model original-a))
        (reverse (elts model original-b))
        (elts model c₁))

LoopObligation :
  (model : StackModel) →
  Stack model Int →
  Stack model Int →
  Set
LoopObligation model original-a original-b =
  (b′₁ a′₁ c₁ b₁ a₁ : Stack model Int) →
  (reverse (elts model original-a) ≡
      reverse (elts model a₁) ++ elts model a′₁
   ∧
   reverse (elts model original-b) ≡
      reverse (elts model b₁) ++ elts model b′₁
   ∧
   Shuffle
      (elts model a′₁)
      (elts model b′₁)
      (elts model c₁)) →
  (first-choice : Bool) →
  ChoiceForFirstTest model a₁ b₁ first-choice →
  LoopContinuation
    model original-a original-b a′₁ b′₁ c₁ a₁ b₁ first-choice

ShuffleVC :
  (model : StackModel) →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Stack model Int →
  Set
ShuffleVC model c a′ b′ a b =
  reverse (elts model a) ≡ reverse (elts model a) ++ elts model a′
  ∧
  reverse (elts model b) ≡ reverse (elts model b) ++ elts model b′
  ∧
  Shuffle (elts model a′) (elts model b′) (elts model c)
  ∧
  LoopObligation model a b

shuffle'vc : Set₁
shuffle'vc =
  (model : StackModel) →
  (c a′ b′ a b : Stack model Int) →
  elts model c ≡ [] →
  elts model a′ ≡ [] →
  elts model b′ ≡ [] →
  ShuffleVC model c a′ b′ a b
