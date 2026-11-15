-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/braun_trees_BraunHeaps_replace_minqtvc: the Braun-heap minimum
-- replacement verification condition preserving heap order, Braun balance,
-- tree size, and element multiplicities. This file contains no proof.

{-# OPTIONS --safe #-}

module braun_trees_BraunHeaps_replace_minqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<Z_ _≢_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

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

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

IfDec : {P : Set} → Dec P → Set → Set → Set
IfDec (yes _) when-true when-false = when-true
IfDec (no _) when-true when-false = when-false

IfBool : {P : Set} → Dec P → Bool → Bool → Bool
IfBool (yes _) when-true when-false = when-true
IfBool (no _) when-true when-false = when-false

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

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

module BraunHeapTheory
  (Elt : Set)
  (eltDefault : Elt)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  (le : Elt → Elt → Set)
  (leRefl : (x : Elt) → le x x)
  (leTrans :
    (x y z : Elt) → le x y → le y z → le x z)
  (leTotal : (x y : Elt) → le x y ∨ le y x)
  where

  decide : (P : Set) → Dec P
  decide P with excludedMiddle P
  ... | left proof = yes proof
  ... | right refutation = no refutation

  data Tree : Set where
    Empty : Tree
    Node  : Tree → Elt → Tree → Tree

  size : Tree → Int
  size Empty = zeroZ
  size (Node l root r) =
    addInt (addInt oneZ (size l)) (size r)

  occ : Elt → Tree → Int
  occ sought Empty = zeroZ
  occ sought (Node l root r) with decide (root ≡ sought)
  ... | yes equality =
    addInt (addInt oneZ (occ sought l)) (occ sought r)
  ... | no inequality =
    addInt (addInt zeroZ (occ sought l)) (occ sought r)

  leRoot : Elt → Tree → Set
  leRoot lower Empty = ⊤
  leRoot lower (Node l root r) = le lower root

  heap : Tree → Set
  heap Empty = ⊤
  heap (Node l root r) =
    leRoot root l ∧
    heap l ∧
    leRoot root r ∧
    heap r

  inv : Tree → Set
  inv Empty = ⊤
  inv (Node l root r) =
    (size l ≡ size r ∨
     size l ≡ addInt (size r) oneZ) ∧
    inv l ∧
    inv r

  minimum : Tree → Elt
  minimum Empty = eltDefault
  minimum (Node l root r) = root

  childMatches : Tree → Tree → Set
  childMatches Empty child = ⊥
  childMatches (Node first root second) child =
    first ≡ child ∨ second ≡ child

  branchFlag : Elt → Tree → Tree → Bool → Set
  branchFlag replacement l r flag =
    IfDec
      (decide (leRoot replacement l))
      (flag ≡ IfBool (decide (leRoot replacement r)) true false)
      (flag ≡ false)

  preservesOtherOccurrences :
    Elt → Elt → Tree → Tree → Set
  preservesOtherOccurrences replacement removed result original =
    (e : Elt) →
    e ≢ replacement →
    e ≢ removed →
    occ e result ≡ occ e original

  rebuiltPremise : Elt → Tree → Tree → Set
  rebuiltPremise replacement original rebuilt =
    heap rebuilt ∧
    inv rebuilt ∧
    IfDec
      (decide (replacement ≡ minimum original))
      (occ replacement rebuilt ≡ occ replacement original)
      (occ replacement rebuilt ≡
         addInt (occ replacement original) oneZ ∧
       occ (minimum original) rebuilt ≡
         subtractInt (occ (minimum original) original) oneZ) ∧
    preservesOtherOccurrences
      replacement (minimum original) rebuilt original ∧
    size rebuilt ≡ size original

  initialObligation : Tree → Elt → Set
  initialObligation Empty replacement = ⊥
  initialObligation whole@(Node l root r) replacement =
    (flag : Bool) →
    branchFlag replacement l r flag →
    Not (flag ≡ true) →
    (heap l ∧ zeroZ <Z size l) ∧
    IfDec
      (decide (leRoot (minimum l) r))
      (childMatches whole l ∧
       heap l ∧
       inv l ∧
       zeroZ <Z size l)
      ((childMatches whole r ∧
        heap r ∧
        inv r ∧
        zeroZ <Z size r) ∧
       ((rebuilt : Tree) →
        rebuiltPremise replacement r rebuilt →
        heap r ∧ zeroZ <Z size r))

  resultPremise : Tree → Elt → Tree → Set
  resultPremise Empty replacement result = ⊥
  resultPremise (Node l root r) replacement result =
    Exists Bool λ flag →
      branchFlag replacement l r flag ∧
      IfDec
        (decide (flag ≡ true))
        (result ≡ Node l replacement r)
        (let leftMinimum = minimum l
         in
         IfDec
           (decide (leRoot leftMinimum r))
           (Exists Tree λ rebuilt →
             rebuiltPremise replacement l rebuilt ∧
             result ≡ Node rebuilt leftMinimum r)
           (Exists Tree λ rebuilt →
             rebuiltPremise replacement r rebuilt ∧
             result ≡ Node l (minimum r) rebuilt))

  resultConclusion : Tree → Elt → Tree → Set
  resultConclusion original replacement result =
    heap result ∧
    inv result ∧
    IfDec
      (decide (replacement ≡ minimum original))
      (occ replacement result ≡ occ replacement original)
      (occ replacement result ≡
         addInt (occ replacement original) oneZ ∧
       occ (minimum original) result ≡
         subtractInt (occ (minimum original) original) oneZ) ∧
    preservesOtherOccurrences
      replacement (minimum original) result original ∧
    size result ≡ size original

  replace-min'vc : Set
  replace-min'vc =
    (t : Tree) →
    (replacement : Elt) →
    heap t →
    inv t →
    zeroZ <Z size t →
    initialObligation t replacement ∧
    ((result : Tree) →
      resultPremise t replacement result →
      resultConclusion t replacement result)
