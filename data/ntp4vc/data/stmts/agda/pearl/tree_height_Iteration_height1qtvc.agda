-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/tree_height_Iteration_height1qtvc: the verification condition for
-- iterative binary-tree height evaluation, including continuation semantics,
-- termination decrease, and final-result correctness. This file contains no proof.

{-# OPTIONS --safe #-}

module tree_height_Iteration_height1qtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

ifBool : Bool → Bool → Bool → Bool
ifBool true whenTrue whenFalse = whenTrue
ifBool false whenTrue whenFalse = whenFalse

IfSet : Bool → Set → Set → Set
IfSet true whenTrue whenFalse = whenTrue
IfSet false whenTrue whenFalse = whenFalse

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) = negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

maxInt : Int → Int → Int
maxInt x y with intLess x y
... | true = y
... | false = x

zeroZ oneZ threeZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
threeZ = pos (suc (suc (suc zero)))
fourZ = pos (suc (suc (suc (suc zero))))

data Tree (A : Set) : Set where
  Empty : Tree A
  Node  : Tree A → A → Tree A → Tree A

size : {A : Set} → Tree A → Int
size Empty = zeroZ
size (Node l value r) =
  addInt (addInt oneZ (size l)) (size r)

height : {A : Set} → Tree A → Int
height Empty = zeroZ
height (Node l value r) =
  addInt oneZ (maxInt (height l) (height r))

data Cont (A : Set) : Set where
  Id     : Cont A
  Kleft  : Tree A → Cont A → Cont A
  Kright : Int → Cont A → Cont A

data What (A : Set) : Set where
  Argument : Tree A → What A
  Result   : Int → What A

isId : {A : Set} → Cont A → Bool
isId Id = true
isId (Kleft _ _) = false
isId (Kright _ _) = false

isResult : {A : Set} → What A → Bool
isResult (Argument _) = false
isResult (Result _) = true

evalk : {A : Set} → Cont A → Int → Int
evalk Id r = r
evalk (Kleft l k₁) r =
  evalk k₁ (addInt oneZ (maxInt (height l) r))
evalk (Kright x k₁) r =
  evalk k₁ (addInt oneZ (maxInt x r))

evalw : {A : Set} → What A → Int
evalw (Argument t) = height t
evalw (Result x) = x

sizek : {A : Set} → Cont A → Int
sizek Id = zeroZ
sizek (Kleft t k₁) =
  addInt
    (addInt threeZ (multiplyInt fourZ (size t)))
    (sizek k₁)
sizek (Kright x k₁) =
  addInt oneZ (sizek k₁)

sizew : {A : Set} → What A → Int
sizew (Argument t) =
  addInt oneZ (multiplyInt fourZ (size t))
sizew (Result _) = zeroZ

measure : {A : Set} → Cont A → What A → Int
measure k w = addInt (sizek k) (sizew w)

controlPremise : {A : Set} → Cont A → What A → Bool → Set
controlPremise k w o₁ =
  IfSet
    (isId k)
    (o₁ ≡ ifBool (isResult w) true false)
    (o₁ ≡ false)

stepObligation :
  {A : Set} → Tree A → Cont A → What A → Cont A → What A → Set
stepObligation t k w nextK nextW =
  ((zeroZ ≤Z measure k w) ∧
   (measure nextK nextW <Z measure k w)) ∧
  (evalk nextK (evalw nextW) ≡ height t)

transitionObligation : {A : Set} → Tree A → Cont A → What A → Set
transitionObligation t k (Argument Empty) =
  stepObligation t k (Argument Empty) k (Result zeroZ)
transitionObligation t k (Argument (Node l value r)) =
  stepObligation
    t
    k
    (Argument (Node l value r))
    (Kleft r k)
    (Argument l)
transitionObligation t Id (Result x) = ⊥
transitionObligation t (Kleft pending k₁) (Result x) =
  stepObligation
    t
    (Kleft pending k₁)
    (Result x)
    (Kright x k₁)
    (Argument pending)
transitionObligation t (Kright leftHeight k₁) (Result rightHeight) =
  stepObligation
    t
    (Kright leftHeight k₁)
    (Result rightHeight)
    k₁
    (Result (addInt oneZ (maxInt leftHeight rightHeight)))

isFinalWhat : {A : Set} → What A → Set
isFinalWhat (Argument _) = ⊥
isFinalWhat (Result _) = ⊤

resultPremise : {A : Set} → What A → Int → Set
resultPremise (Argument _) result = ⊥
resultPremise (Result r) result = result ≡ r

finalObligation : {A : Set} → Tree A → What A → Set
finalObligation t w =
  isFinalWhat w ∧
  ((result : Int) →
    resultPremise w result →
    result ≡ height t)

controlConclusion :
  {A : Set} → Tree A → Cont A → What A → Bool → Set
controlConclusion t k w false = transitionObligation t k w
controlConclusion t k w true = finalObligation t w

height1'vc : Set₁
height1'vc =
  (A : Set) →
  (default : A) →
  (t : Tree A) →
  (evalk (Id {A = A}) (evalw (Argument t)) ≡ height t) ∧
  ((k : Cont A) →
    (w : What A) →
    evalk k (evalw w) ≡ height t →
    (o₁ : Bool) →
    controlPremise k w o₁ →
    controlConclusion t k w o₁)
