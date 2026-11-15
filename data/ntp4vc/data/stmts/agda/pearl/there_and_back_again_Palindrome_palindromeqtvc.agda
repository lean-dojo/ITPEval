-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/there_and_back_again_Palindrome_palindromeqtvc: the palindrome
-- verification condition, including normal-return preservation and the
-- consequence of an internally witnessed mismatching index. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module there_and_back_again_Palindrome_palindromeqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≤N_ _≤Z_ _<Z_
infixl 6 _-Z_
infixr 5 _++_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record Inhabited (A : Set) : Set where
  constructor inhabited
  field
    witness : A

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

data _≤N_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤N n
  suc≤suc : {m n : Nat} → m ≤N n → suc m ≤N suc n

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

negateInt : Int → Int
negateInt (pos zero) = pos zero
negateInt (pos (suc n)) = negsuc n
negateInt (negsuc n) = pos (suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

_-Z_ : Int → Int → Int
_-Z_ = subtractInt

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

natToInt : Nat → Int
natToInt = pos

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

nthNat : {A : Set} → Nat → List A → Maybe A
nthNat zero [] = nothing
nthNat zero (x ∷ xs) = just x
nthNat (suc n) [] = nothing
nthNat (suc n) (_ ∷ xs) = nthNat n xs

nthInt : {A : Set} → List A → Int → Maybe A
nthInt xs i = nthNat (intToNat i) xs

IndexBounds : Int → Int → Set
IndexBounds i n =
  zeroZ ≤Z i ∧ i <Z n

Pal : {A : Set} → List A → Int → Set
Pal xs n =
  (i : Int) →
  IndexBounds i n →
  nthInt xs i ≡ nthInt xs (n -Z oneZ -Z i)

NotPal : {A : Set} → List A → Int → Set
NotPal xs n =
  Σ Int λ i →
    IndexBounds i n
    ∧ Not (nthInt xs i ≡ nthInt xs (n -Z oneZ -Z i))

EqSpec :
  {A : Set} →
  (A → A → Bool) →
  Set
EqSpec {A} eq =
  (x y : A) →
  (eq x y ≡ true) ↔ (x ≡ y)

PrefixWitness :
  {A : Set} →
  List A →
  List A →
  Set
PrefixWitness whole suffix =
  Σ (List _) λ prefix →
    length prefix ≡ length whole
    ∧ whole ≡ prefix ++ suffix

palindrome'vc : Set₁
palindrome'vc =
  (Elt : Set) →
  Inhabited Elt →
  (eq : Elt → Elt → Bool) →
  EqSpec eq →
  (x : List Elt) →
  length x ≤N length x
  ∧
  ((o₁ : List Elt) →
   (PrefixWitness x o₁ ∧ Pal x (natToInt (length x))) →
   Pal x (natToInt (length x)))
  ∧
  (NotPal x (natToInt (length x)) →
   Not (Pal x (natToInt (length x))))
