-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_lexicographic_permutations_1_Top_swapqtvc: the
-- integer-array swap verification condition exchanging two designated
-- entries, preserving every other entry, and preserving permutation
-- occurrence counts after conversion to a sequence. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021LexicographicPermutations1TopSwapVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤Z_ _<Z_ _≢_
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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

zeroZ : Int
zeroZ = pos zero

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] index value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc index) value =
  x ∷ setAt xs index value

ifInt : Bool → Int → Int → Int
ifInt true when-true when-false = when-true
ifInt false when-true when-false = when-false

updateInt :
  (Int → Int) →
  Int →
  Int →
  Int →
  Int
updateInt values index value query =
  ifInt (intEqual query index) value (values query)

Bounds : Int → List Int → Set
Bounds index xs =
  zeroZ ≤Z index ∧ index <Z lengthZ xs

countInt : Int → List Int → Nat
countInt value [] = zero
countInt value (x ∷ xs) with intEqual value x
... | true = suc (countInt value xs)
... | false = countInt value xs

occAll : Int → List Int → Int
occAll value xs = pos (countInt value xs)

record SequenceModel : Set where
  field
    toSeq : List Int → List Int
    toSeq-length :
      (array : List Int) →
      length (toSeq array) ≡ length array
    toSeq-index :
      (array : List Int) →
      (index : Int) →
      zeroZ ≤Z index →
      index <Z lengthZ (toSeq array) →
      nthInt (toSeq array) index ≡ nthInt array index

open SequenceModel

IsPermutationOf :
  SequenceModel →
  List Int →
  List Int →
  Set
IsPermutationOf model permutation original =
  length permutation ≡ length original
  ∧
  ((value : Int) →
    occAll value permutation ≡ occAll value original)

PointwiseUpdate :
  List Int →
  List Int →
  Int →
  Int →
  Set
PointwiseUpdate newer older index value =
  (query : Int) →
  nthInt newer query ≡
  updateInt (nthInt older) index value query

UnchangedExcept :
  List Int →
  List Int →
  Int →
  Int →
  Set
UnchangedExcept newer older first-index second-index =
  (index : Int) →
  Bounds index newer →
  index ≢ first-index →
  index ≢ second-index →
  nthInt newer index ≡ nthInt older index

SwapConsequences :
  SequenceModel →
  List Int →
  List Int →
  Int →
  Int →
  Set
SwapConsequences model original swapped i j =
  nthInt swapped i ≡ nthInt original j
  ∧
  nthInt swapped j ≡ nthInt original i
  ∧
  UnchangedExcept swapped original i j
  ∧
  IsPermutationOf model
    (toSeq model swapped)
    (toSeq model original)

SwapConclusion :
  SequenceModel →
  Int →
  List Int →
  Int →
  Set
SwapConclusion model i original j =
  zeroZ ≤Z i
  ∧
  i <Z lengthZ original
  ∧
  (let temp = nthInt original i
   in
   (zeroZ ≤Z j ∧ j <Z lengthZ original)
   ∧
   (let other = nthInt original j
        first-update =
          setAt original (toNat i) other
    in
    (zeroZ ≤Z i ∧ i <Z lengthZ original)
    ∧
    (length first-update ≡ length original →
     PointwiseUpdate first-update original i other →
     (zeroZ ≤Z j ∧ j <Z lengthZ first-update)
     ∧
     (let swapped =
            setAt first-update (toNat j) temp
      in
      length swapped ≡ length first-update →
      PointwiseUpdate swapped first-update j temp →
      SwapConsequences model original swapped i j))))

swap'vc : Set
swap'vc =
  (model : SequenceModel) →
  (i : Int) →
  (original : List Int) →
  (j : Int) →
  zeroZ ≤Z i →
  i <Z lengthZ original →
  zeroZ ≤Z j →
  j <Z lengthZ original →
  SwapConclusion model i original j
