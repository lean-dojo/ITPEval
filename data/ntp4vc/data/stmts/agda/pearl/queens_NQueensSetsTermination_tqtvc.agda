-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/queens_NQueensSetsTermination_tqtvc: the finite-integer-set
-- termination verification condition for the recursive N-queens search and
-- its nested set-removal loop. This file contains no proof.

{-# OPTIONS --safe #-}

module queens_NQueensSetsTermination_tqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

contains : Int → List Int → Bool
contains x [] = false
contains x (y ∷ ys) with intEqual x y
... | true = true
... | false = contains x ys

removeAll : Int → List Int → List Int
removeAll x [] = []
removeAll x (y ∷ ys) with intEqual x y
... | true = removeAll x ys
... | false = y ∷ removeAll x ys

nub : List Int → List Int
nub [] = []
nub (x ∷ xs) with contains x xs
... | true = nub xs
... | false = x ∷ nub xs

differenceList : List Int → List Int → List Int
differenceList [] ys = []
differenceList (x ∷ xs) ys with contains x ys
... | true = differenceList xs ys
... | false = x ∷ differenceList xs ys

record FSet : Set where
  constructor fset
  field
    elements : List Int

open FSet

empty : FSet
empty = fset []

memberBool : Int → FSet → Bool
memberBool x set = contains x (elements set)

member : Int → FSet → Set
member x set = memberBool x set ≡ true

subset : FSet → FSet → Set
subset leftSet rightSet =
  (x : Int) → member x leftSet → member x rightSet

setEqual : FSet → FSet → Set
setEqual leftSet rightSet =
  subset leftSet rightSet ∧ subset rightSet leftSet

Nonempty : FSet → Set
Nonempty set = Not (setEqual set empty)

difference : FSet → FSet → FSet
difference leftSet rightSet =
  fset (differenceList (elements leftSet) (elements rightSet))

insert : Int → FSet → FSet
insert x set with memberBool x set
... | true = set
... | false = fset (x ∷ elements set)

erase : Int → FSet → FSet
erase x set = fset (removeAll x (elements set))

card : FSet → Nat
card set = length (nub (elements set))

cardZ : FSet → Int
cardZ set = pos (card set)

minimumPair : Int → Int → Int
minimumPair x y with intLessOrEqual x y
... | true = x
... | false = y

minimumFrom : Int → List Int → Int
minimumFrom current [] = current
minimumFrom current (x ∷ xs) =
  minimumFrom (minimumPair current x) xs

minimum : FSet → Int
minimum set with elements set
... | [] = zeroZ
... | x ∷ xs = minimumFrom x xs

InsertCondition : Int → FSet → FSet → Set
InsertCondition d base result =
  setEqual result (insert d base)
  ∧
  IfSet
    (memberBool d base)
    (cardZ result ≡ cardZ base)
    (cardZ result ≡ addInt (cardZ base) oneZ)

RemoveCondition : Int → FSet → FSet → Set
RemoveCondition d base result =
  setEqual result (erase d base)
  ∧
  IfSet
    (memberBool d base)
    (cardZ result ≡ subtractInt (cardZ base) oneZ)
    (cardZ result ≡ cardZ base)

SuccessorSetCondition : FSet → FSet → Set
SuccessorSetCondition source result =
  (i : Int) →
  member i result ↔
    (zeroZ ≤Z i ∧ member (addInt i oneZ) source)

PredecessorSetCondition : FSet → FSet → Set
PredecessorSetCondition source result =
  (i : Int) →
  member i result ↔
    (oneZ ≤Z i ∧ member (subtractInt i oneZ) source)

InnerRemoval :
  FSet →
  FSet →
  FSet →
  FSet →
  Int →
  Set
InnerRemoval a b c e d =
  (o3 : FSet) →
  InsertCondition d c o3 →
  (o4 : FSet) →
  SuccessorSetCondition o3 o4 →
  (o5 : FSet) →
  InsertCondition d b o5 →
  (o6 : FSet) →
  PredecessorSetCondition o5 o6 →
  (o7 : FSet) →
  RemoveCondition d a o7 →
  ((zeroZ ≤Z cardZ a ∧ cardZ o7 <Z cardZ a)
   ∧
   ((o8 : Int) →
    (o9 : FSet) →
    RemoveCondition d e o9 →
    ((zeroZ ≤Z cardZ e ∧ cardZ o9 <Z cardZ e)
     ∧ subset o9 (difference (difference a b) c))))

IterationCondition : FSet → FSet → FSet → FSet → Set
IterationCondition a b c e =
  Nonempty e
  ∧
  let d = minimum e
  in InnerRemoval a b c e d

t'vc : Set
t'vc =
  (a o1 b o2 c : FSet) →
  Nonempty a →
  setEqual o1 (difference a b) →
  setEqual o2 (difference o1 c) →
  subset o2 (difference (difference a b) c)
  ∧
  ((f : Int) →
   (e : FSet) →
   subset e (difference (difference a b) c) →
   Nonempty e →
   IterationCondition a b c e)
