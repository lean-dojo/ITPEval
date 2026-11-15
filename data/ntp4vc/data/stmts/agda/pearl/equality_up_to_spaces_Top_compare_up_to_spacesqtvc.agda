-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/equality_up_to_spaces_Top_compare_up_to_spacesqtvc: the loop
-- verification condition for comparing two character lists after recursively
-- removing spaces. This file contains no proof.

{-# OPTIONS --safe #-}

module equality_up_to_spaces_Top_compare_up_to_spacesqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixl 6 _+Z_ _-Z_
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

ifBool : {A : Set} → Bool → A → A → A
ifBool true whenTrue whenFalse = whenTrue
ifBool false whenTrue whenFalse = whenFalse

IfBoolSet : Bool → Set → Set → Set
IfBoolSet true whenTrue whenFalse = whenTrue
IfBoolSet false whenTrue whenFalse = whenFalse

notBool : Bool → Bool
notBool true = false
notBool false = true

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc n) = true
natLess (suc m) zero = false
natLess (suc m) (suc n) = natLess m n

natLessEqual : Nat → Nat → Bool
natLessEqual zero n = true
natLessEqual (suc m) zero = false
natLessEqual (suc m) (suc n) = natLessEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos m) (negsuc n) = false
intEqual (negsuc m) (pos n) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos m) (negsuc n) = false
intLess (negsuc m) (pos n) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessEqual : Int → Int → Bool
intLessEqual (pos m) (pos n) = natLessEqual m n
intLessEqual (pos m) (negsuc n) = false
intLessEqual (negsuc m) (pos n) = true
intLessEqual (negsuc m) (negsuc n) = natLessEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessEqual x y ≡ true

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

_+Z_ : Int → Int → Int
_+Z_ = addInt

_-Z_ : Int → Int → Int
_-Z_ = subtractInt

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

natToInt : Nat → Int
natToInt = pos

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc n) = zero

lengthList : {A : Set} → List A → Nat
lengthList [] = zero
lengthList (_ ∷ xs) = suc (lengthList xs)

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] n = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc n) =
  indexDefault default xs n

EqSpec :
  {Char : Set} →
  (Char → Char → Bool) →
  Set
EqSpec {Char} eq =
  (x y : Char) →
  (eq x y ≡ true) ↔ (x ≡ y)

RemoveSpacesDef :
  {Char : Set} →
  Char →
  Char →
  (Char → Char → Bool) →
  (List Char → List Char) →
  Set
RemoveSpacesDef default space eq removeSpaces =
  (s : List _) →
  IfBoolSet
    (natEqual (lengthList s) zero)
    (removeSpaces s ≡ s)
    (IfBoolSet
      (eq (indexDefault default s zero) space)
      (removeSpaces s ≡ removeSpaces (dropList (suc zero) s))
      (removeSpaces s ≡
        indexDefault default s zero ∷
        removeSpaces (dropList (suc zero) s)))

Bounds : Int → Int → Set
Bounds index length =
  zeroZ ≤Z index ∧ index ≤Z length

Invariant :
  {Char : Set} →
  (List Char → List Char) →
  List Char →
  List Char →
  Int →
  Int →
  Set
Invariant removeSpaces x y i j =
  (removeSpaces x ≡ removeSpaces y) ↔
  (removeSpaces (dropList (intToNat i) x) ≡
   removeSpaces (dropList (intToNat j) y))

measure : Int → Int → Int → Int → Int
measure n m i j =
  n -Z i +Z m -Z j

MeasureDecreasesX : Int → Int → Int → Int → Set
MeasureDecreasesX n m i j =
  zeroZ ≤Z measure n m i j ∧
  measure n m (i +Z oneZ) j <Z measure n m i j

MeasureDecreasesY : Int → Int → Int → Int → Set
MeasureDecreasesY n m i j =
  zeroZ ≤Z measure n m i j ∧
  measure n m i (j +Z oneZ) <Z measure n m i j

MeasureDecreasesBoth : Int → Int → Int → Int → Set
MeasureDecreasesBoth n m i j =
  zeroZ ≤Z measure n m i j ∧
  measure n m (i +Z oneZ) (j +Z oneZ) <Z measure n m i j

StepX :
  {Char : Set} →
  (List Char → List Char) →
  List Char →
  List Char →
  Int →
  Int →
  Int →
  Int →
  Set
StepX removeSpaces x y n m i j =
  MeasureDecreasesX n m i j ∧
  Bounds (i +Z oneZ) n ∧
  Bounds j m ∧
  Invariant removeSpaces x y (i +Z oneZ) j

StepY :
  {Char : Set} →
  (List Char → List Char) →
  List Char →
  List Char →
  Int →
  Int →
  Int →
  Int →
  Set
StepY removeSpaces x y n m i j =
  MeasureDecreasesY n m i j ∧
  Bounds i n ∧
  Bounds (j +Z oneZ) m ∧
  Invariant removeSpaces x y i (j +Z oneZ)

StepBoth :
  {Char : Set} →
  (List Char → List Char) →
  List Char →
  List Char →
  Int →
  Int →
  Int →
  Int →
  Set
StepBoth removeSpaces x y n m i j =
  MeasureDecreasesBoth n m i j ∧
  Bounds (i +Z oneZ) n ∧
  Bounds (j +Z oneZ) m ∧
  Invariant removeSpaces x y (i +Z oneZ) (j +Z oneZ)

HeadIsSpaceCondition :
  {Char : Set} →
  Char →
  Char →
  (Char → Char → Bool) →
  List Char →
  Int →
  Bool →
  Set
HeadIsSpaceCondition default space eq xs i answer =
  let current = indexDefault default xs (intToNat i)
  in
  answer ≡ eq current space ∧
  ((answer ≡ true) ↔ (current ≡ space))

LoopBody :
  {Char : Set} →
  Char →
  Char →
  (Char → Char → Bool) →
  (List Char → List Char) →
  List Char →
  List Char →
  Int →
  Int →
  Int →
  Int →
  Set
LoopBody default space eq removeSpaces x y n m i j =
  (o1 : Bool) →
  IfBoolSet
    (intLess i n)
    (o1 ≡ true)
    (o1 ≡ ifBool (intLess j m) true false) →
  IfBoolSet
    o1
    ((o2 : Bool) →
      IfBoolSet
        (intLess i n)
        (HeadIsSpaceCondition default space eq x i o2)
        (o2 ≡ false) →
      IfBoolSet
        o2
        (StepX removeSpaces x y n m i j)
        ((o3 : Bool) →
          IfBoolSet
            (intLess j m)
            (HeadIsSpaceCondition default space eq y j o3)
            (o3 ≡ false) →
          IfBoolSet
            o3
            (StepY removeSpaces x y n m i j)
            ((o4 : Bool) →
              IfBoolSet
                (intEqual i n)
                (o4 ≡ true)
                (o4 ≡ ifBool (intEqual j m) true false) →
              IfBoolSet
                o4
                (Not (removeSpaces x ≡ removeSpaces y))
                (let currentY = indexDefault default y (intToNat j)
                     currentX = indexDefault default x (intToNat i)
                     o7 = eq currentX currentY
                 in
                 ((o7 ≡ true) ↔ (currentX ≡ currentY)) →
                 IfBoolSet
                   (notBool o7)
                   (Not (removeSpaces x ≡ removeSpaces y))
                   (StepBoth removeSpaces x y n m i j)))))
    (removeSpaces x ≡ removeSpaces y)

CompareUpToSpacesVC :
  {Char : Set} →
  Char →
  Char →
  (Char → Char → Bool) →
  (List Char → List Char) →
  List Char →
  List Char →
  Set
CompareUpToSpacesVC default space eq removeSpaces x y =
  let n = natToInt (lengthList x)
      m = natToInt (lengthList y)
  in
  (Bounds zeroZ n ∧
   Bounds zeroZ m ∧
   Invariant removeSpaces x y zeroZ zeroZ) ∧
  ((j i : Int) →
    (Bounds i n ∧
     Bounds j m ∧
     Invariant removeSpaces x y i j) →
    LoopBody default space eq removeSpaces x y n m i j)

compare-up-to-spaces'vc : Set₁
compare-up-to-spaces'vc =
  (Char : Set) →
  (default space : Char) →
  (eq : Char → Char → Bool) →
  EqSpec eq →
  (removeSpaces : List Char → List Char) →
  RemoveSpacesDef default space eq removeSpaces →
  (x y : List Char) →
  CompareUpToSpacesVC default space eq removeSpaces x y
