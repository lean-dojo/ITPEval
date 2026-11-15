-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vstte12_combinators_Combinators_reduction3qtvc: the recursive
-- verification condition for call-by-value reduction of iterated K-combinator
-- applications, including the parity characterization of the resulting value.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module vstte12_combinators_Combinators_reduction3qtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _⟶_
infixr 3 _∧_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

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

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

evenNat : Nat → Bool
oddNat : Nat → Bool
evenNat zero = true
evenNat (suc n) = oddNat n
oddNat zero = false
oddNat (suc n) = evenNat n

evenInt : Int → Bool
evenInt (pos n) = evenNat n
evenInt (negsuc n) = evenNat (suc n)

oddInt : Int → Bool
oddInt (pos n) = oddNat n
oddInt (negsuc n) = oddNat (suc n)

Even : Int → Set
Even n = evenInt n ≡ true

Odd : Int → Set
Odd n = oddInt n ≡ true

data Term : Set where
  S   : Term
  K   : Term
  App : Term → Term → Term

IsValue : Term → Set
IsValue K = ⊤
IsValue S = ⊤
IsValue (App K value) = IsValue value
IsValue (App S value) = IsValue value
IsValue (App (App S value₁) value₂) =
  IsValue value₁ ∧ IsValue value₂
IsValue _ = ⊥

data Context : Set where
  Hole  : Context
  Left  : Context → Term → Context
  Right : Term → Context → Context

IsContext : Context → Set
IsContext Hole = ⊤
IsContext (Left context _) = IsContext context
IsContext (Right value context) =
  IsValue value ∧ IsContext context

subst : Context → Term → Term
subst Hole term = term
subst (Left context term₂) term =
  App (subst context term) term₂
subst (Right value₁ context) term =
  App value₁ (subst context term)

data _⟶_ : Term → Term → Set where
  reduce-K :
    (context : Context) →
    (value₁ value₂ : Term) →
    IsContext context →
    IsValue value₁ →
    IsValue value₂ →
    subst context (App (App K value₁) value₂) ⟶
      subst context value₁

  reduce-S :
    (context : Context) →
    (value₁ value₂ value₃ : Term) →
    IsContext context →
    IsValue value₁ →
    IsValue value₂ →
    IsValue value₃ →
    subst context (App (App (App S value₁) value₂) value₃) ⟶
      subst context (App (App value₁ value₃) (App value₂ value₃))

data RelTR : Term → Term → Set where
  base-trans-refl :
    (term : Term) →
    RelTR term term

  step-trans-refl :
    (start middle finish : Term) →
    RelTR start middle →
    middle ⟶ finish →
    RelTR start finish

substC : Context → Context → Context
substC Hole inserted = inserted
substC (Left context term₂) inserted =
  Left (substC context inserted) term₂
substC (Right value₁ context) inserted =
  Right value₁ (substC context inserted)

ksNat : Nat → Term
ksNat zero = K
ksNat (suc n) = App (ksNat n) K

ks : Int → Term
ks (pos n) = ksNat n
ks (negsuc _) = K

KHeadShape : Term → Set
KHeadShape K = ⊤
KHeadShape (App K _) = ⊤
KHeadShape _ = ⊥

ReductionResult : Term → Term → Term → Set
ReductionResult K value₂ result =
  result ≡ App K value₂
ReductionResult (App K value₃) _ result =
  result ≡ value₃
ReductionResult _ _ _ = ⊥

InitialCondition : Int → Context → Set
InitialCondition n context with ks n
... | K = ⊤
... | S = ⊥
... | App term₁ term₂ =
  let
    predecessor = subtractInt n oneZ
    leftContext = Left Hole term₂
    recursiveContext = substC context leftContext
  in
  ((IsContext context ∧ IsContext leftContext) →
    IsContext recursiveContext) →
  (((zeroZ ≤Z n ∧ predecessor <Z n) ∧
    zeroZ ≤Z predecessor ∧
    term₁ ≡ ks predecessor ∧
    IsContext recursiveContext) ∧
   ((value₁ : Term) →
    (RelTR
       (subst recursiveContext term₁)
       (subst recursiveContext value₁) ∧
     IsValue value₁ ∧
     (Even predecessor → value₁ ≡ K) ∧
     (Odd predecessor → value₁ ≡ App K K)) →
    let
      rightContext = Right value₁ Hole
      finalContext = substC context rightContext
    in
    ((IsContext context ∧ IsContext rightContext) →
      IsContext finalContext) →
    (((zeroZ ≤Z n ∧ zeroZ <Z n) ∧
      zeroZ ≤Z zeroZ ∧
      term₂ ≡ ks zeroZ ∧
      IsContext finalContext) ∧
     ((value₂ : Term) →
      (RelTR
         (subst finalContext term₂)
         (subst finalContext value₂) ∧
       IsValue value₂ ∧
       (Even zeroZ → value₂ ≡ K) ∧
       (Odd zeroZ → value₂ ≡ App K K)) →
      KHeadShape value₁))))

ResultPremise : Int → Context → Term → Set
ResultPremise n context result with ks n
... | K = result ≡ K
... | S = ⊥
... | App term₁ term₂ =
  let
    predecessor = subtractInt n oneZ
    leftContext = Left Hole term₂
    recursiveContext = substC context leftContext
  in
  (((IsContext context ∧ IsContext leftContext) →
      IsContext recursiveContext) ∧
   Exists Term λ value₁ →
     ((RelTR
        (subst recursiveContext term₁)
        (subst recursiveContext value₁) ∧
       IsValue value₁ ∧
       (Even predecessor → value₁ ≡ K) ∧
       (Odd predecessor → value₁ ≡ App K K)) ∧
      let
        rightContext = Right value₁ Hole
        finalContext = substC context rightContext
      in
      (((IsContext context ∧ IsContext rightContext) →
          IsContext finalContext) ∧
       Exists Term λ value₂ →
         ((RelTR
            (subst finalContext term₂)
            (subst finalContext value₂) ∧
           IsValue value₂ ∧
           (Even zeroZ → value₂ ≡ K) ∧
           (Odd zeroZ → value₂ ≡ App K K)) ∧
          ReductionResult value₁ value₂ result))))

reduction3-vc : Set
reduction3-vc =
  (n : Int) →
  (context : Context) →
  zeroZ ≤Z n →
  IsContext context →
  InitialCondition n context ∧
  ((result : Term) →
   ResultPremise n context result →
   (RelTR (subst context (ks n)) (subst context result) ∧
    IsValue result ∧
    (Even n → result ≡ K) ∧
    (Odd n → result ≡ App K K)))
