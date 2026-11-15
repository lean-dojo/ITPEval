-- Statement-only formalization of VERINA corpus artifact verina_advanced_62,
-- catalog title "rain": a deterministic two-pointer program computes trapped
-- rainwater on a nonnegative integer elevation list and is connected to the
-- prefix/suffix-maximum summation contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced62 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

chooseSet : Bool → Set → Set → Set
chooseSet true when-true when-false = when-true
chooseSet false when-true when-false = when-false

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natGreaterOrEqual : Nat → Nat → Bool
natGreaterOrEqual m n = natLessOrEqual n m

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual x y =
  if intLess y x
  then false
  else true

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intPredecessor : Int → Int
intPredecessor (pos zero) = negsuc zero
intPredecessor (pos (suc n)) = pos n
intPredecessor (negsuc n) = negsuc (suc n)

intAdd : Int → Int → Int
intAdd x (pos zero) = x
intAdd x (pos (suc n)) =
  intSuccessor (intAdd x (pos n))
intAdd x (negsuc zero) = intPredecessor x
intAdd x (negsuc (suc n)) =
  intPredecessor (intAdd x (negsuc n))

intNegate : Int → Int
intNegate (pos zero) = pos zero
intNegate (pos (suc n)) = negsuc n
intNegate (negsuc n) = pos (suc n)

intSubtract : Int → Int → Int
intSubtract x y = intAdd x (intNegate y)

intMax : Int → Int → Int
intMax x y =
  if intLess x y
  then y
  else x

intMin : Int → Int → Int
intMin x y =
  if intLess x y
  then x
  else y

zeroInt : Int
zeroInt = pos zero

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

nonnegative : Int → Bool
nonnegative value = intLessOrEqual zeroInt value

rain-precond : List Int → Set
rain-precond heights =
  IsTrue (allList nonnegative heights)

rainAuxWithFuel :
  Nat →
  List Int →
  Nat →
  Nat →
  Int →
  Int →
  Int →
  Int
rainAuxWithFuel zero heights left right leftMax rightMax water =
  water
rainAuxWithFuel
  (suc fuel)
  heights
  left
  right
  leftMax
  rightMax
  water =
  if natGreaterOrEqual left right
  then water
  else
    let left-height = nthDefault zeroInt left heights
        right-height = nthDefault zeroInt right heights
    in
      if intLessOrEqual left-height right-height
      then (
        let new-left-max = intMax leftMax left-height
            new-water =
              intAdd
                water
                (intMax
                  zeroInt
                  (intSubtract leftMax left-height))
        in
          rainAuxWithFuel
            fuel
            heights
            (suc left)
            right
            new-left-max
            rightMax
            new-water)
      else (
        let new-right-max = intMax rightMax right-height
            new-water =
              intAdd
                water
                (intMax
                  zeroInt
                  (intSubtract rightMax right-height))
        in
          rainAuxWithFuel
            fuel
            heights
            left
            (predecessor right)
            leftMax
            new-right-max
            new-water)

three : Nat
three = suc (suc (suc zero))

rain :
  (heights : List Int) →
  rain-precond heights →
  Int
rain heights h-precond =
  let n = listLength heights
  in
    if natLess n three
    then zeroInt
    else
      rainAuxWithFuel
        n
        heights
        zero
        (predecessor n)
        (nthDefault zeroInt zero heights)
        (nthDefault zeroInt (predecessor n) heights)
        zeroInt

maxLeftLoop :
  Nat →
  Nat →
  List Int →
  Int →
  Int
maxLeftLoop zero index heights maximum = maximum
maxLeftLoop (suc fuel) index heights maximum =
  maxLeftLoop
    fuel
    (suc index)
    heights
    (intMax maximum (nthDefault zeroInt index heights))

maxLeftAt : List Int → Nat → Int
maxLeftAt heights index =
  maxLeftLoop (suc index) zero heights zeroInt

maxListFromZero : List Int → Int
maxListFromZero [] = zeroInt
maxListFromZero (x ∷ xs) =
  intMax x (maxListFromZero xs)

maxRightAt : List Int → Nat → Int
maxRightAt heights index =
  maxListFromZero (dropList index heights)

waterAt : List Int → Nat → Int
waterAt heights index =
  intMax
    zeroInt
    (intSubtract
      (intMin
        (maxLeftAt heights index)
        (maxRightAt heights index))
      (nthDefault zeroInt index heights))

sumWaterFrom :
  List Int →
  Nat →
  Int →
  List Int →
  Int
sumWaterFrom heights index accumulator [] = accumulator
sumWaterFrom heights index accumulator (_ ∷ xs) =
  sumWaterFrom
    heights
    (suc index)
    (intAdd accumulator (waterAt heights index))
    xs

sumWater : List Int → Int
sumWater heights =
  sumWaterFrom heights zero zeroInt heights

rain-postcond :
  (heights : List Int) →
  (result : Int) →
  rain-precond heights →
  Set
rain-postcond heights result h-precond =
  IsTrue (intLessOrEqual zeroInt result) ∧
  chooseSet
    (natLess (listLength heights) three)
    (result ≡ zeroInt)
    (result ≡ sumWater heights)

rain-spec-satisfied : Set
rain-spec-satisfied =
  (heights : List Int) →
  (h-precond : rain-precond heights) →
  rain-postcond
    heights
    (rain heights h-precond)
    h-precond
