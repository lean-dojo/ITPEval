-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/kmp_KnuthMorrisPratt_initnextqtvc: the Knuth-Morris-Pratt
-- initialization verification condition for constructing the next table
-- while preserving prefix-match invariants and loop variants. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module kmp_KnuthMorrisPratt_initnextqtvc where

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

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

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

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

updateFunction : (Int → Int) → Int → Int → Int → Int
updateFunction old index value query =
  IfInt (intEqual query index) value (old query)

PointwiseEqual : {A B : Set} → (A → B) → (A → B) → Set
PointwiseEqual f g =
  (x : _) → f x ≡ g x

UpdateCondition :
  List Int →
  Int →
  Int →
  Set →
  Set
UpdateCondition xs index value conclusion =
  length (setAt xs (toNat index) value) ≡ length xs →
  PointwiseEqual
    (nthInt (setAt xs (toNat index) value))
    (updateFunction (nthInt xs) index value) →
  conclusion

InBounds : {A : Set} → List A → Int → Set
InBounds xs index =
  zeroZ ≤Z index ∧ index <Z lengthZ xs

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
  Matches a₁ i₁ a₂ i₂ n =
    (zeroZ ≤Z i₁ ∧ i₁ ≤Z subtractInt (lengthZ a₁) n)
    ∧
    (zeroZ ≤Z i₂ ∧ i₂ ≤Z subtractInt (lengthZ a₂) n)
    ∧
    ((i : Int) →
      (zeroZ ≤Z i ∧ i <Z n) →
      nthChar a₁ (addInt i₁ i) ≡
        nthChar a₂ (addInt i₂ i))

  IsNext : List Char → Int → Int → Set
  IsNext p j n =
    (zeroZ ≤Z n ∧ n <Z j)
    ∧ Matches p (subtractInt j n) p zeroZ n
    ∧
    ((z : Int) →
      (n <Z z ∧ z <Z j) →
      Not (Matches p (subtractInt j z) p zeroZ z))

  LoopInvariant :
    List Char →
    Int →
    List Int →
    Int →
    Int →
    Set
  LoopInvariant p m next j i =
    (zeroZ ≤Z j ∧ j <Z i ∧ i ≤Z m)
    ∧ Matches p (subtractInt i j) p zeroZ j
    ∧
    ((z : Int) →
      (addInt j oneZ <Z z ∧
       z <Z addInt i oneZ) →
      Not
        (Matches
          p
          (subtractInt (addInt i oneZ) z)
          p
          zeroZ
          z))
    ∧
    ((k : Int) →
      (zeroZ <Z k ∧ k ≤Z i) →
      IsNext p k (nthInt next k))

  FinalState : List Char → List Int → Set
  FinalState p next =
    length next ≡ length p
    ∧
    ((j : Int) →
      (zeroZ <Z j ∧ j <Z lengthZ p) →
      IsNext p j (nthInt next j))

  EqualDecrease : Int → Int → Int → Set
  EqualDecrease m i j =
    (zeroZ ≤Z subtractInt m i
     ∧ subtractInt m (addInt i oneZ) <Z subtractInt m i)
    ∨
    (subtractInt m i ≡ subtractInt m (addInt i oneZ)
     ∧ zeroZ ≤Z j
     ∧ addInt j oneZ <Z j)

  ZeroDecrease : Int → Int → Int → Set
  ZeroDecrease m i j =
    (zeroZ ≤Z subtractInt m i
     ∧ subtractInt m (addInt i oneZ) <Z subtractInt m i)
    ∨
    (subtractInt m i ≡ subtractInt m (addInt i oneZ)
     ∧ zeroZ ≤Z j
     ∧ j <Z j)

  FallbackDecrease :
    Int →
    Int →
    Int →
    List Int →
    Set
  FallbackDecrease m i j next =
    (zeroZ ≤Z subtractInt m i
     ∧ subtractInt m i <Z subtractInt m i)
    ∨
    (zeroZ ≤Z j ∧ nthInt next j <Z j)

  EqualBranch :
    List Char →
    Int →
    Int →
    Int →
    List Int →
    Set
  EqualBranch p m j i next =
    let nextIndex = addInt i oneZ
        nextValue = addInt j oneZ
        updated = setAt next (toNat nextIndex) nextValue
    in
    InBounds next nextIndex
    ∧
    UpdateCondition
      next
      nextIndex
      nextValue
      (EqualDecrease m i j
       ∧ LoopInvariant
           p
           m
           updated
           (addInt j oneZ)
           (addInt i oneZ))

  ZeroBranch :
    List Char →
    Int →
    Int →
    Int →
    List Int →
    Set
  ZeroBranch p m j i next =
    let nextIndex = addInt i oneZ
        updated = setAt next (toNat nextIndex) zeroZ
    in
    InBounds next nextIndex
    ∧
    UpdateCondition
      next
      nextIndex
      zeroZ
      (ZeroDecrease m i j
       ∧ LoopInvariant
           p
           m
           updated
           j
           (addInt i oneZ))

  FallbackBranch :
    List Char →
    Int →
    Int →
    Int →
    List Int →
    Set
  FallbackBranch p m j i next =
    InBounds next j
    ∧ FallbackDecrease m i j next
    ∧ LoopInvariant p m next (nthInt next j) i

  CharacterStep :
    List Char →
    Int →
    Int →
    Int →
    List Int →
    Set
  CharacterStep p m j i next =
    InBounds p j
    ∧ InBounds p i
    ∧
    IfCharEqual
      (nthChar p i)
      (nthChar p j)
      (EqualBranch p m j i next)
      (IfSet
        (intEqual j zeroZ)
        (ZeroBranch p m j i next)
        (FallbackBranch p m j i next))

  LoopConclusion :
    List Char →
    Int →
    Int →
    Int →
    List Int →
    Set
  LoopConclusion p m j i next =
    IfSet
      (intLess i (subtractInt m oneZ))
      (CharacterStep p m j i next)
      (FinalState p next)

  LoopStep :
    List Char →
    Int →
    List Int →
    Set
  LoopStep p m initial =
    (j i : Int) →
    (next : List Int) →
    length next ≡ length initial →
    LoopInvariant p m next j i →
    LoopConclusion p m j i next

  NontrivialInitialization :
    List Char →
    Int →
    List Int →
    Set
  NontrivialInitialization p m next =
    let updated = setAt next (toNat oneZ) zeroZ
    in
    InBounds next oneZ
    ∧
    UpdateCondition
      next
      oneZ
      zeroZ
      (LoopInvariant p m updated zeroZ oneZ
       ∧ LoopStep p m updated)

  InitializedWithZero : List Int → Int → Set
  InitializedWithZero next m =
    ((i : Int) →
      (zeroZ ≤Z i ∧ i <Z m) →
      nthInt next i ≡ zeroZ)
    ∧ lengthZ next ≡ m

  InitNextBody : List Char → Set
  InitNextBody p =
    let m = lengthZ p
    in
    zeroZ ≤Z m
    ∧
    ((next : List Int) →
      InitializedWithZero next m →
      IfSet
        (intLess oneZ m)
        (NontrivialInitialization p m next)
        (FinalState p next))

  initnext-vc : Set
  initnext-vc =
    (p : List Char) →
    oneZ ≤Z lengthZ p →
    InitNextBody p
