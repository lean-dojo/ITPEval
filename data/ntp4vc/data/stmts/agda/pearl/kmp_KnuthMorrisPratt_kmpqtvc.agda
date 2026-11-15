-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/kmp_KnuthMorrisPratt_kmpqtvc: the Knuth-Morris-Pratt search
-- verification condition preserving prefix-match invariants and establishing
-- the first occurrence of a pattern. This file contains no proof.

{-# OPTIONS --safe #-}

module kmp_KnuthMorrisPratt_kmpqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
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

IfDec : {P : Set} → Dec P → Set → Set → Set
IfDec (yes _) when-true when-false = when-true
IfDec (no _) when-true when-false = when-false

IfBool : Bool → Bool → Bool → Bool
IfBool true when-true when-false = when-true
IfBool false when-true when-false = when-false

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

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

module KMPTheory
  (Char : Set)
  (charDefault : Char)
  (charDecEq : (x y : Char) → Dec (x ≡ y))
  where

  nthChar : List Char → Int → Char
  nthChar xs index =
    nthDefault charDefault (toNat index) xs

  IfCharEqual : Char → Char → Set → Set → Set
  IfCharEqual x y when-equal when-different =
    IfDec (charDecEq x y) when-equal when-different

  Matches :
    List Char →
    Int →
    List Char →
    Int →
    Int →
    Set
  Matches a₁ i₁ a₂ i₂ count =
    (zeroZ ≤Z i₁ ∧ i₁ ≤Z subtractInt (lengthZ a₁) count)
    ∧
    (zeroZ ≤Z i₂ ∧ i₂ ≤Z subtractInt (lengthZ a₂) count)
    ∧
    ((offset : Int) →
      (zeroZ ≤Z offset ∧ offset <Z count) →
      nthChar a₁ (addInt i₁ offset) ≡
        nthChar a₂ (addInt i₂ offset))

  IsNext : List Char → Int → Int → Set
  IsNext p j nextValue =
    (zeroZ ≤Z nextValue ∧ nextValue <Z j)
    ∧ Matches p (subtractInt j nextValue) p zeroZ nextValue
    ∧
    ((z : Int) →
      (nextValue <Z z ∧ z <Z j) →
      Not (Matches p (subtractInt j z) p zeroZ z))

  FirstOccur : List Char → List Char → Int → Set
  FirstOccur p a result =
    ((zeroZ ≤Z result ∧ result <Z lengthZ a) →
      Matches a result p zeroZ (lengthZ p))
    ∧
    ((k : Int) →
      (zeroZ ≤Z k ∧ k <Z result) →
      Not (Matches a k p zeroZ (lengthZ p)))

  NextTableValid : List Char → List Int → Set
  NextTableValid p next =
    length next ≡ length p
    ∧
    ((j : Int) →
      (zeroZ <Z j ∧ j <Z lengthZ p) →
      IsNext p j (nthInt next j))

  SearchInvariant :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    Int →
    Set
  SearchInvariant p a m n j i =
    ((zeroZ ≤Z j ∧ j ≤Z m) ∧ j ≤Z i ∧ i ≤Z n)
    ∧ Matches a (subtractInt i j) p zeroZ j
    ∧
    ((k : Int) →
      (zeroZ ≤Z k ∧ k <Z subtractInt i j) →
      Not (Matches a k p zeroZ m))

  InitialInvariant :
    List Char →
    List Char →
    Int →
    Int →
    Set
  InitialInvariant p a m n =
    ((zeroZ ≤Z zeroZ ∧ zeroZ ≤Z m)
      ∧ zeroZ ≤Z zeroZ ∧ zeroZ ≤Z n)
    ∧ Matches a (subtractInt zeroZ zeroZ) p zeroZ zeroZ
    ∧
    ((k : Int) →
      (zeroZ ≤Z k ∧
       k <Z subtractInt zeroZ zeroZ) →
      Not (Matches a k p zeroZ m))

  EqualDecrease : Int → Int → Int → Set
  EqualDecrease n i j =
    (zeroZ ≤Z subtractInt n i
      ∧
      subtractInt n (addInt i oneZ) <Z subtractInt n i)
    ∨
    (subtractInt n i ≡ subtractInt n (addInt i oneZ)
      ∧ zeroZ ≤Z j
      ∧ addInt j oneZ <Z j)

  ZeroDecrease : Int → Int → Int → Set
  ZeroDecrease n i j =
    (zeroZ ≤Z subtractInt n i
      ∧
      subtractInt n (addInt i oneZ) <Z subtractInt n i)
    ∨
    (subtractInt n i ≡ subtractInt n (addInt i oneZ)
      ∧ zeroZ ≤Z j
      ∧ j <Z j)

  FallbackDecrease :
    Int →
    Int →
    Int →
    List Int →
    Set
  FallbackDecrease n i j next =
    (zeroZ ≤Z subtractInt n i
      ∧ subtractInt n i <Z subtractInt n i)
    ∨
    (zeroZ ≤Z j ∧ nthInt next j <Z j)

  EqualBranch :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    Int →
    List Int →
    Set
  EqualBranch p a m n j i next =
    EqualDecrease n i j
    ∧ SearchInvariant
        p a m n (addInt j oneZ) (addInt i oneZ)

  ZeroBranch :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    Int →
    List Int →
    Set
  ZeroBranch p a m n j i next =
    ZeroDecrease n i j
    ∧ SearchInvariant p a m n j (addInt i oneZ)

  FallbackBranch :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    Int →
    List Int →
    Set
  FallbackBranch p a m n j i next =
    (zeroZ ≤Z j ∧ j <Z lengthZ next)
    ∧ FallbackDecrease n i j next
    ∧ SearchInvariant p a m n (nthInt next j) i

  CharacterStep :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    Int →
    List Int →
    Set
  CharacterStep p a m n j i next =
    (zeroZ ≤Z j ∧ j <Z lengthZ p)
    ∧ (zeroZ ≤Z i ∧ i <Z lengthZ a)
    ∧
    IfCharEqual
      (nthChar a i)
      (nthChar p j)
      (EqualBranch p a m n j i next)
      (IfSet
        (intEqual j zeroZ)
        (ZeroBranch p a m n j i next)
        (FallbackBranch p a m n j i next))

  FinalResult :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    Set
  FinalResult p a m j i =
    (result : Int) →
    IfSet
      (intEqual j m)
      (result ≡ subtractInt i m)
      (result ≡ i) →
    FirstOccur p a result

  LoopConclusion :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    Int →
    List Int →
    Bool →
    Set
  LoopConclusion p a m n j i next o₁ =
    IfSet
      o₁
      (CharacterStep p a m n j i next)
      (FinalResult p a m j i)

  GuardValue : Int → Int → Int → Int → Bool
  GuardValue m n j i =
    IfBool
      (intLess j m)
      (IfBool (intLess i n) true false)
      false

  LoopStep :
    List Char →
    List Char →
    Int →
    Int →
    List Int →
    Set
  LoopStep p a m n next =
    (j i : Int) →
    SearchInvariant p a m n j i →
    (o₁ : Bool) →
    o₁ ≡ GuardValue m n j i →
    LoopConclusion p a m n j i next o₁

  SearchBody : List Char → List Char → Set
  SearchBody p a =
    let m = lengthZ p
        n = lengthZ a
    in
    oneZ ≤Z lengthZ p
    ∧
    ((next : List Int) →
      NextTableValid p next →
      InitialInvariant p a m n
      ∧ LoopStep p a m n next)

  kmp-vc : Set
  kmp-vc =
    (p a : List Char) →
    oneZ ≤Z lengthZ p →
    SearchBody p a
