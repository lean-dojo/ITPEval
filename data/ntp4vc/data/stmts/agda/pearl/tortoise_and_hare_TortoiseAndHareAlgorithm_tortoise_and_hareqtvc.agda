-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/tortoise_and_hare_TortoiseAndHareAlgorithm_tortoise_and_hareqtvc:
-- the Floyd tortoise-and-hare cycle-detection verification condition,
-- including both loop invariants and the final cycle witnesses. This file contains no proof.

{-# OPTIONS --safe #-}

module tortoise_and_hare_TortoiseAndHareAlgorithm_tortoise_and_hareqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

ifBool : Bool → Bool → Bool → Bool
ifBool true when-true when-false = when-true
ifBool false when-true when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

iterateNat : (Int → Int) → Nat → Int → Int
iterateNat f zero value = value
iterateNat f (suc n) value = f (iterateNat f n value)

record TortoiseModel : Set where
  field
    f          : Int → Int
    m          : Int
    m-positive : zeroZ <Z m
    f-range    :
      (value : Int) →
      zeroZ ≤Z value →
      value <Z m →
      zeroZ ≤Z f value ∧ f value <Z m
    x0         : Int
    x0-range   : zeroZ ≤Z x0 ∧ x0 <Z m

open TortoiseModel

x : TortoiseModel → Int → Int
x model i =
  iterateNat (f model) (toNat i) (x0 model)

DistinctBefore :
  TortoiseModel →
  Int →
  Set
DistinctBefore model bound =
  (i j : Int) →
  (zeroZ ≤Z i ∧ i <Z j ∧ j <Z bound) →
  x model i ≢ x model j

NoTortoiseHareMeetingBefore :
  TortoiseModel →
  Int →
  Set
NoTortoiseHareMeetingBefore model bound =
  (i : Int) →
  (oneZ ≤Z i ∧ i <Z bound) →
  x model i ≢ x model (multiplyInt twoZ i)

FirstLoopAdvance :
  TortoiseModel →
  Int →
  Int →
  Set
FirstLoopAdvance model cycleBound n =
  Not (cycleBound <Z addInt n oneZ)
  ∧
  (Not (cycleBound <Z addInt n oneZ) →
   (zeroZ ≤Z subtractInt cycleBound n
    ∧ subtractInt cycleBound (addInt n oneZ)
        <Z subtractInt cycleBound n)
   ∧
   (oneZ ≤Z addInt n oneZ
    ∧ addInt n oneZ ≤Z cycleBound)
   ∧ f model (x model n) ≡ x model (addInt n oneZ)
   ∧ f model (f model (x model (multiplyInt twoZ n)))
       ≡ x model (multiplyInt twoZ (addInt n oneZ))
   ∧ NoTortoiseHareMeetingBefore model (addInt n oneZ))

NoEarlierOffsetMeeting :
  TortoiseModel →
  Int →
  Int →
  Set
NoEarlierOffsetMeeting model n i =
  (j : Int) →
  (zeroZ ≤Z j ∧ j <Z i) →
  x model j ≢ x model (addInt n j)

NoEarlierReturnToN :
  TortoiseModel →
  Int →
  Int →
  Set
NoEarlierReturnToN model n i =
  (j : Int) →
  (zeroZ <Z j ∧ j <Z i) →
  x model (addInt n j) ≢ x model n

SecondLoopInitial :
  TortoiseModel →
  Int →
  Int →
  Set
SecondLoopInitial model mu n =
  (zeroZ ≤Z zeroZ ∧ zeroZ ≤Z mu)
  ∧ (x0 model ≡ x model zeroZ
     ∧ x model n ≡ x model (addInt n zeroZ))
  ∧ NoEarlierOffsetMeeting model n zeroZ
  ∧ NoEarlierReturnToN model n zeroZ

candidateFlag :
  TortoiseModel →
  Int →
  Int →
  Bool
candidateFlag model n i =
  ifBool
    (intLess zeroZ i)
    (intEqual (x model (addInt n i)) (x model n))
    false

SecondLoopAdvanceCommon :
  TortoiseModel →
  Int →
  Int →
  Int →
  Set
SecondLoopAdvanceCommon model mu n i =
  (zeroZ ≤Z subtractInt mu i
   ∧ subtractInt mu (addInt i oneZ)
       <Z subtractInt mu i)
  ∧
  (zeroZ ≤Z addInt i oneZ
   ∧ addInt i oneZ ≤Z mu)
  ∧
  (f model (x model i) ≡ x model (addInt i oneZ)
   ∧ f model (x model (addInt n i))
       ≡ x model (addInt n (addInt i oneZ)))
  ∧ NoEarlierOffsetMeeting model n (addInt i oneZ)

SecondLoopAdvance :
  TortoiseModel →
  Int →
  Int →
  Int →
  Int →
  Int →
  Bool →
  Set
SecondLoopAdvance model mu lambda n lam i o1 =
  SecondLoopAdvanceCommon model mu n i
  ∧
  IfSet
    o1
    (IfSet
      (intEqual i zeroZ)
      (NoEarlierReturnToN model n (addInt i oneZ))
      (i ≡ lambda))
    (IfSet
      (intEqual lam zeroZ)
      (NoEarlierReturnToN model n (addInt i oneZ))
      (lam ≡ lambda))

FlagDefinition :
  TortoiseModel →
  Int →
  Int →
  Bool →
  Int →
  Set
FlagDefinition model n lam o1 i =
  IfSet
    (intEqual lam zeroZ)
    (o1 ≡ candidateFlag model n i)
    (o1 ≡ false)

CycleWitness :
  TortoiseModel →
  Int →
  Int →
  Set
CycleWitness model i l =
  ((zeroZ ≤Z i ∧ i <Z m model)
   ∧ (oneZ ≤Z l ∧ l ≤Z m model)
   ∧ addInt i l ≤Z m model
   ∧ x model (addInt i l) ≡ x model i)
  ∧ DistinctBefore model (addInt i l)

SecondLoopStop :
  TortoiseModel →
  Int →
  Int →
  Int →
  Set
SecondLoopStop model n lam i =
  (l : Int) →
  IfSet
    (intEqual lam zeroZ)
    (l ≡ n)
    (l ≡ lam)
  →
  CycleWitness model i l

SecondLoopStep :
  TortoiseModel →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
SecondLoopStep model mu lambda n lam i =
  IfSet
    (notBool
      (intEqual
        (x model i)
        (x model (addInt n i))))
    ((o1 : Bool) →
     FlagDefinition model n lam o1 i →
     SecondLoopAdvance model mu lambda n lam i o1)
    (SecondLoopStop model n lam i)

SecondLoopInvariant :
  TortoiseModel →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
SecondLoopInvariant model mu lambda n lam i =
  (zeroZ ≤Z i ∧ i ≤Z mu)
  ∧ NoEarlierOffsetMeeting model n i
  ∧
  IfSet
    (intEqual lam zeroZ)
    (NoEarlierReturnToN model n i)
    (lam ≡ lambda)

SecondLoopPackage :
  TortoiseModel →
  Int →
  Int →
  Int →
  Set
SecondLoopPackage model mu lambda n =
  SecondLoopInitial model mu n
  ∧
  ((lam i : Int) →
   SecondLoopInvariant model mu lambda n lam i →
   SecondLoopStep model mu lambda n lam i)

FirstLoopStep :
  TortoiseModel →
  Int →
  Int →
  Int →
  Int →
  Set
FirstLoopStep model mu lambda cycleBound n =
  ((oneZ ≤Z n ∧ n ≤Z cycleBound)
   ∧ NoTortoiseHareMeetingBefore model n)
  →
  IfSet
    (notBool
      (intEqual
        (x model n)
        (x model (multiplyInt twoZ n))))
    (FirstLoopAdvance model cycleBound n)
    (SecondLoopPackage model mu lambda n)

TortoiseAndHareConclusion :
  TortoiseModel →
  Int →
  Int →
  Set
TortoiseAndHareConclusion model mu lambda =
  let cycleBound = addInt mu lambda
  in
  oneZ ≤Z oneZ
  ∧ oneZ ≤Z cycleBound
  ∧ f model (x0 model) ≡ x model oneZ
  ∧ f model (f model (x0 model))
      ≡ x model (multiplyInt twoZ oneZ)
  ∧ NoTortoiseHareMeetingBefore model oneZ
  ∧
  ((n : Int) →
   FirstLoopStep model mu lambda cycleBound n)

tortoise-and-hare'vc : Set
tortoise-and-hare'vc =
  (model : TortoiseModel) →
  (mu lambda : Int) →
  zeroZ ≤Z mu →
  mu <Z m model →
  oneZ ≤Z lambda →
  lambda ≤Z m model →
  addInt mu lambda ≤Z m model →
  x model (addInt mu lambda) ≡ x model mu →
  DistinctBefore model (addInt mu lambda) →
  TortoiseAndHareConclusion model mu lambda
