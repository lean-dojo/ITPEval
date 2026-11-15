-- Statement-only formalization of VERINA corpus artifact verina_basic_81,
-- catalog title "DivisionFunction": a deterministic natural-number division
-- program returns a remainder-quotient integer pair, including its zero-divisor
-- branch, and is connected to its division correctness contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic81 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infix 4 _≠_ _≤z_ _<z_
infixr 3 _∧_
infixr 4 _,_
infixr 5 _×_
infixl 6 _+z_
infixl 7 _*z_

record Top : Set where
  constructor top

data Empty : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → Empty

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first-conjunct : A
    second-conjunct : B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    pairFirst : A
    pairSecond : B

open _×_ public

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

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
intLessOrEqual (negsuc m) (negsuc n) =
  natLessOrEqual n m

_≤z_ : Int → Int → Set
x ≤z y = IsTrue (intLessOrEqual x y)

_<z_ : Int → Int → Set
x <z y = IsTrue (intLess x y)

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

ofNat : Nat → Int
ofNat = pos

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

divMod : Nat → Nat → Int × Int
divMod x y =
  ofNat (naturalMod x y) , ofNat (naturalDiv x y)

DivisionFunction-precond : Nat → Nat → Set
DivisionFunction-precond x y = Top

DivisionFunction :
  (x y : Nat) →
  DivisionFunction-precond x y →
  Int × Int
DivisionFunction x y h-precond =
  if natEqual y zero
  then ofNat x , pos zero
  else divMod x y

DivisionFunction-postcond :
  (x y : Nat) →
  (result : Int × Int) →
  DivisionFunction-precond x y →
  Set
DivisionFunction-postcond x y result h-precond =
  (y ≡ zero →
    (pairFirst result ≡ ofNat x) ∧
    (pairSecond result ≡ pos zero)) ∧
  (y ≠ zero →
    ((pairSecond result *z ofNat y) +z pairFirst result ≡ ofNat x) ∧
    ((pos zero ≤z pairFirst result) ∧
     (pairFirst result <z ofNat y)) ∧
    (pos zero ≤z pairSecond result))

DivisionFunction-spec-satisfied : Set
DivisionFunction-spec-satisfied =
  (x y : Nat) →
  (h-precond : DivisionFunction-precond x y) →
  DivisionFunction-postcond
    x
    y
    (DivisionFunction x y h-precond)
    h-precond
