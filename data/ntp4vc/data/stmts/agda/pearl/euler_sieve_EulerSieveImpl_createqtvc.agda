-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/euler_sieve_EulerSieveImpl_createqtvc: the integer and signed
-- 63-bit verification condition for constructing the initial Euler-sieve
-- arrays and their invariants. This file contains no proof.

{-# OPTIONS --safe #-}

module euler_sieve_EulerSieveImpl_createqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

ifSet : Bool → Set → Set → Set
ifSet true A B = A
ifSet false A B = B

ifInt : Bool → Int → Int → Int
ifInt true x y = x
ifInt false x y = y

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

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
multiplyInt (pos m) (negsuc n) = negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) = negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

absoluteInt : Int → Int
absoluteInt (pos n) = pos n
absoluteInt (negsuc n) = pos (suc n)

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

modTwoNat : Nat → Nat
modTwoNat zero = zero
modTwoNat (suc zero) = suc zero
modTwoNat (suc (suc n)) = modTwoNat n

-- Truncation toward zero, used for signed machine-integer conversion.
tdivTwo : Int → Int
tdivTwo (pos n) = pos (halfNat n)
tdivTwo (negsuc n) = negative (halfNat (suc n))

-- Euclidean quotient and remainder by the positive divisor two.
edivTwo : Int → Int
edivTwo (pos n) = pos (halfNat n)
edivTwo (negsuc n) = negative (halfNat (suc (suc n)))

emodTwo : Int → Int
emodTwo (pos n) = pos (modTwoNat n)
emodTwo (negsuc n) = pos (modTwoNat (suc n))

zeroZ oneZ twoZ threeZ : Int
zeroZ = pos zero
oneZ = pos 1
twoZ = pos 2
threeZ = pos 3

minusTwoZ max63 min63 : Int
minusTwoZ = negsuc 1
max63 = pos 4611686018427387903
min63 = negsuc 4611686018427387903

In63 : Int → Set
In63 x = min63 ≤Z x ∧ x ≤Z max63

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

lengthNat : {A : Set} → List A → Nat
lengthNat [] = zero
lengthNat (_ ∷ xs) = suc (lengthNat xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (lengthNat xs)

nthDefault : {A : Set} → A → List A → Nat → A
nthDefault d [] _ = d
nthDefault d (x ∷ xs) zero = x
nthDefault d (x ∷ xs) (suc n) = nthDefault d xs n

nthInt : List Int → Int → Int
nthInt xs i = nthDefault zeroZ xs (toNat i)

nthBool : List Bool → Int → Bool
nthBool xs i = nthDefault false xs (toNat i)

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ a = []
setAt (x ∷ xs) zero a = a ∷ xs
setAt (x ∷ xs) (suc n) a = x ∷ setAt xs n a

setList : {A : Set} → List A → Int → A → List A
setList xs i a = setAt xs (toNat i) a

createFrom : {A : Set} → Nat → Nat → (Int → A) → List A
createFrom zero k f = []
createFrom (suc n) k f = f (pos k) ∷ createFrom n (suc k) f

createList : {A : Set} → Int → (Int → A) → List A
createList n f = createFrom (toNat n) zero f

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false b = b

andBool : Bool → Bool → Bool
andBool true b = b
andBool false _ = false

fc : Int → Int → Int
fc max1 i =
  ifInt (intEqual i max1)
    (addInt max1 oneZ)
    (ifInt (intEqual i (subtractInt max1 oneZ))
      (ifInt (intEqual (emodTwo i) zeroZ)
        max1
        (addInt max1 oneZ))
      (ifInt
        (orBool (intLess i threeZ)
          (intEqual (emodTwo i) zeroZ))
        (addInt i oneZ)
        (addInt i twoZ)))

o1 : Int → Bool
o1 i =
  orBool (intEqual i zeroZ)
    (orBool (intEqual i oneZ)
      (andBool (intLess twoZ i)
        (intEqual (emodTwo i) zeroZ)))

fc1 : Int → Int → Int → Int
fc1 max1 lenArr i =
  ifInt (intEqual i (subtractInt lenArr oneZ))
    (addInt max1 oneZ)
    (ifInt (intEqual i zeroZ)
      minusTwoZ
      (addInt (multiplyInt twoZ i) threeZ))

record RawContext : Set₁ where
  field
    Array63 Result : Set
    defaultArray : Array63
    defaultResult : Result
    arrayElts : Array63 → List Int
    arraySize : Array63 → Int
    resultNexts : Result → List Int
    resultMarked : Result → List Bool
    resultArr : Result → Array63
    resultMax : Result → Int
    resultMaxArr : Result → Int

open RawContext

InvNexts : List Int → Int → Set
InvNexts nexts n =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z n →
  i <Z nthInt nexts i ∧ nthInt nexts i ≤Z n

EliminatedBetween : List Bool → List Int → Int → Set
EliminatedBetween marked nexts i =
  (j : Int) →
  i <Z j ∧ j <Z nthInt nexts i →
  nthBool marked j ≡ true

AllEliminatedMarked : List Bool → List Int → Set
AllEliminatedMarked marked nexts =
  lengthZ marked ≡ lengthZ nexts
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i <Z lengthZ marked →
    EliminatedBetween marked nexts i)

ArrayInvariant : (ctx : RawContext) → Array63 ctx → Set
ArrayInvariant ctx a =
  zeroZ ≤Z arraySize ctx a
  ∧ arraySize ctx a ≡ lengthZ (arrayElts ctx a)
  ∧ lengthZ (arrayElts ctx a) ≤Z max63
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i <Z lengthZ (arrayElts ctx a) →
    In63 (nthInt (arrayElts ctx a) i))

ResultInvariantIndex : (ctx : RawContext) → Result ctx → Set
ResultInvariantIndex ctx self =
  let marked = resultMarked ctx self
      nexts = resultNexts ctx self
      els = arrayElts ctx (resultArr ctx self)
      maximum = resultMax ctx self
      maximumArr = resultMaxArr ctx self
  in
  ((i : Int) →
    threeZ ≤Z i ∧ i ≤Z maximum →
    emodTwo i ≡ zeroZ →
    nthBool marked i ≡ true)
  ∧
  ((i : Int) →
    threeZ ≤Z i ∧ i <Z subtractInt maximum oneZ →
    emodTwo i ≡ oneZ →
    emodTwo (nthInt nexts i) ≡ oneZ
    ∨ nthInt nexts i ≡ addInt maximum oneZ)
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i ≤Z maximumArr →
    negateInt (addInt maximum oneZ) ≤Z nthInt els i
    ∧ nthInt els i ≤Z addInt maximum oneZ)
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i ≤Z maximumArr →
    (nthBool marked (addInt (multiplyInt twoZ i) oneZ) ≡ true)
    ↔
    (nthInt els i <Z zeroZ))
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i ≤Z maximumArr →
    nthBool marked (addInt (multiplyInt twoZ i) oneZ) ≠ true →
    nthInt els i ≡
      nthInt nexts (addInt (multiplyInt twoZ i) oneZ))
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i ≤Z maximumArr →
    nthBool marked (addInt (multiplyInt twoZ i) oneZ) ≡ true →
    nthInt els i ≡
      negateInt (nthInt nexts (addInt (multiplyInt twoZ i) oneZ)))
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i ≤Z maximumArr →
    (i <Z edivTwo (absoluteInt (nthInt els i))
     ∧ edivTwo (absoluteInt (nthInt els i))
       ≤Z addInt maximumArr oneZ)
    ∧ absoluteInt (nthInt els i) ≤Z addInt maximum oneZ)
  ∧
  ((i j : Int) →
    zeroZ ≤Z i ∧ i ≤Z maximumArr →
    i <Z j ∧ j <Z edivTwo (absoluteInt (nthInt els i)) →
    nthInt els j <Z zeroZ)

ResultInvariant : (ctx : RawContext) → Result ctx → Set
ResultInvariant ctx self =
  let marked = resultMarked ctx self
      nexts = resultNexts ctx self
      els = arrayElts ctx (resultArr ctx self)
      maximum = resultMax ctx self
      maximumArr = resultMaxArr ctx self
  in
  maximum <Z max63
  ∧ threeZ ≤Z maximum
  ∧ lengthZ nexts ≡ lengthZ marked
  ∧ lengthZ marked ≡ addInt maximum oneZ
  ∧ edivTwo (subtractInt maximum oneZ) ≡ maximumArr
  ∧ lengthZ els ≡ addInt maximumArr oneZ
  ∧ InvNexts nexts (lengthZ nexts)
  ∧ AllEliminatedMarked marked nexts
  ∧ ResultInvariantIndex ctx self
  ∧ nthInt nexts maximum ≡ addInt maximum oneZ
  ∧
    (emodTwo (subtractInt maximum oneZ) ≡ zeroZ →
     nthInt nexts (subtractInt maximum oneZ) ≡ maximum)
  ∧
    (emodTwo (subtractInt maximum oneZ) ≡ oneZ →
     nthInt nexts (subtractInt maximum oneZ)
       ≡ addInt maximum oneZ)

ResultFieldsEqual : (ctx : RawContext) → Result ctx → Result ctx → Set
ResultFieldsEqual ctx a b =
  resultNexts ctx a ≡ resultNexts ctx b
  ∧ resultMarked ctx a ≡ resultMarked ctx b
  ∧ resultArr ctx a ≡ resultArr ctx b
  ∧ resultMax ctx a ≡ resultMax ctx b
  ∧ resultMaxArr ctx a ≡ resultMaxArr ctx b

ContextValid : RawContext → Set
ContextValid ctx =
  ((a : Array63 ctx) → ArrayInvariant ctx a)
  ∧ ((r : Result ctx) → In63 (resultMax ctx r))
  ∧ ((r : Result ctx) → In63 (resultMaxArr ctx r))
  ∧ ((r : Result ctx) → ResultInvariant ctx r)
  ∧
  ((a b : Result ctx) →
    ResultFieldsEqual ctx a b →
    a ≡ b)

PostInvariantIndex :
  (ctx : RawContext) →
  Array63 ctx →
  List Int →
  List Bool →
  Int →
  Int →
  Set
PostInvariantIndex ctx arrX nexts marked max1 o8 =
  let els = arrayElts ctx arrX
  in
  ((i : Int) →
    threeZ ≤Z i ∧ i ≤Z max1 →
    emodTwo i ≡ zeroZ →
    nthBool marked i ≡ true)
  ∧
  ((i : Int) →
    threeZ ≤Z i ∧ i <Z subtractInt max1 oneZ →
    emodTwo i ≡ oneZ →
    emodTwo (nthInt nexts i) ≡ oneZ
    ∨ nthInt nexts i ≡ addInt max1 oneZ)
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i ≤Z o8 →
    negateInt (addInt max1 oneZ) ≤Z nthInt els i
    ∧ nthInt els i ≤Z addInt max1 oneZ)
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i ≤Z o8 →
    (nthBool marked (addInt (multiplyInt twoZ i) oneZ) ≡ true)
    ↔
    (nthInt els i <Z zeroZ))
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i ≤Z o8 →
    nthBool marked (addInt (multiplyInt twoZ i) oneZ) ≠ true →
    nthInt els i ≡
      nthInt nexts (addInt (multiplyInt twoZ i) oneZ))
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i ≤Z o8 →
    nthBool marked (addInt (multiplyInt twoZ i) oneZ) ≡ true →
    nthInt els i ≡
      negateInt (nthInt nexts (addInt (multiplyInt twoZ i) oneZ)))
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i ≤Z o8 →
    (i <Z edivTwo (absoluteInt (nthInt els i))
     ∧ edivTwo (absoluteInt (nthInt els i)) ≤Z addInt o8 oneZ)
    ∧ absoluteInt (nthInt els i) ≤Z addInt max1 oneZ)
  ∧
  ((i j : Int) →
    zeroZ ≤Z i ∧ i ≤Z o8 →
    i <Z j ∧ j <Z edivTwo (absoluteInt (nthInt els i)) →
    nthInt els j <Z zeroZ)

ResultIndexProperties : (ctx : RawContext) → Result ctx → Int → Set
ResultIndexProperties ctx result max1 =
  let marked = resultMarked ctx result
      nexts = resultNexts ctx result
  in
  ((i : Int) →
    oneZ ≤Z i
    ∧ i ≤Z edivTwo (subtractInt max1 oneZ) →
    nthBool marked (addInt (multiplyInt twoZ i) oneZ) ≠ true)
  ∧
  ((i : Int) →
    twoZ ≤Z i
    ∧ i ≤Z edivTwo (addInt max1 oneZ) →
    multiplyInt twoZ i ≤Z max1 →
    nthBool marked (multiplyInt twoZ i) ≡ true)
  ∧
  ((i : Int) →
    oneZ ≤Z i
    ∧ i ≤Z edivTwo (subtractInt max1 oneZ) →
    addInt (multiplyInt twoZ i) oneZ
      <Z subtractInt max1 oneZ →
    nthInt nexts (addInt (multiplyInt twoZ i) oneZ)
      ≡ addInt (multiplyInt twoZ i) threeZ)
  ∧
  ((i : Int) →
    twoZ ≤Z i
    ∧ i ≤Z edivTwo (subtractInt max1 oneZ) →
    multiplyInt twoZ i <Z subtractInt max1 oneZ →
    nthInt nexts (multiplyInt twoZ i)
      ≡ addInt (multiplyInt twoZ i) oneZ)
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i ≤Z max1 →
    nthBool marked i ≡ true →
    i <Z twoZ ∨ emodTwo i ≡ zeroZ)

ResultProperties : (ctx : RawContext) → Result ctx → Int → Set
ResultProperties ctx result max1 =
  let marked = resultMarked ctx result
  in
  resultMax ctx result ≡ max1
  ∧
  ((nthBool marked zeroZ ≡ nthBool marked oneZ
    ∧ nthBool marked oneZ ≡ true)
   ∧ nthBool marked twoZ ≠ true)
  ∧ ResultIndexProperties ctx result max1

AllResults :
  (ctx : RawContext) →
  Array63 ctx →
  List Int →
  List Bool →
  Int →
  Int →
  Set
AllResults ctx arrX nexts marked max1 o8 =
  (result : Result ctx) →
  resultNexts ctx result ≡ nexts
  ∧ resultMarked ctx result ≡ marked
  ∧ resultArr ctx result ≡ arrX
  ∧ resultMax ctx result ≡ max1
  ∧ resultMaxArr ctx result ≡ o8 →
  ResultProperties ctx result max1

CompletePostcondition :
  (ctx : RawContext) →
  Array63 ctx →
  List Int →
  List Bool →
  Int →
  Int →
  Set
CompletePostcondition ctx arrX nexts marked max1 o8 =
  (max1 <Z max63 ∧ threeZ ≤Z max1)
  ∧
  (lengthZ nexts ≡ lengthZ marked
   ∧ lengthZ marked ≡ addInt max1 oneZ)
  ∧ edivTwo (subtractInt max1 oneZ) ≡ o8
  ∧ lengthZ (arrayElts ctx arrX) ≡ addInt o8 oneZ
  ∧ InvNexts nexts (lengthZ nexts)
  ∧ AllEliminatedMarked marked nexts
  ∧ PostInvariantIndex ctx arrX nexts marked max1 o8
  ∧ nthInt nexts max1 ≡ addInt max1 oneZ
  ∧
    (emodTwo (subtractInt max1 oneZ) ≡ zeroZ →
     nthInt nexts (subtractInt max1 oneZ) ≡ max1)
  ∧
    (emodTwo (subtractInt max1 oneZ) ≡ oneZ →
     nthInt nexts (subtractInt max1 oneZ) ≡ addInt max1 oneZ)
  ∧ AllResults ctx arrX nexts marked max1 o8

PostO8 :
  (ctx : RawContext) →
  Array63 ctx →
  List Int →
  List Bool →
  Int →
  Int →
  Set
PostO8 ctx arrX nexts marked max1 o7 =
  (o8 : Int) →
  In63 o8 →
  o8 ≡ tdivTwo o7 →
  CompletePostcondition ctx arrX nexts marked max1 o8

PostO7 :
  (ctx : RawContext) →
  Array63 ctx →
  List Int →
  List Bool →
  Int →
  Set
PostO7 ctx arrX nexts marked max1 =
  (o7 : Int) →
  In63 o7 →
  o7 ≡ subtractInt max1 oneZ →
  twoZ ≠ zeroZ
  ∧ In63 (tdivTwo o7)
  ∧ PostO8 ctx arrX nexts marked max1 o7

PostLoop :
  (ctx : RawContext) →
  Array63 ctx →
  List Int →
  List Bool →
  Int →
  Set
PostLoop ctx arrX nexts marked max1 =
  In63 (subtractInt max1 oneZ)
  ∧ PostO7 ctx arrX nexts marked max1

UpdateWitnessCondition : Int → Int → Set
UpdateWitnessCondition i o8 =
  Exists Int
    (λ o9 →
      In63 o9
      ∧ o9 ≡ multiplyInt twoZ i
      ∧ o8 ≡ addInt o9 threeZ)

LoopO8Condition : Int → Int → Int → Int → Set
LoopO8Condition i o7 o8 max1 =
  ifSet (intEqual i o7)
    (o8 ≡ addInt max1 oneZ)
    (UpdateWitnessCondition i o8)

PrefixFc1 :
  (ctx : RawContext) →
  Array63 ctx →
  Int →
  Int →
  Int →
  Set
PrefixFc1 ctx arrX max1 lenArr upper =
  (j : Int) →
  zeroZ ≤Z j ∧ j <Z upper →
  nthInt (arrayElts ctx arrX) j ≡ fc1 max1 lenArr j

AllUpdatedArrays :
  (ctx : RawContext) →
  Array63 ctx →
  Int →
  Int →
  Int →
  Int →
  Set
AllUpdatedArrays ctx arr2 max1 lenArr i o8 =
  (arr3 : Array63 ctx) →
  arraySize ctx arr3 ≡ arraySize ctx arr2 →
  arrayElts ctx arr3 ≡ setList (arrayElts ctx arr2) i o8 →
  PrefixFc1 ctx arr3 max1 lenArr (addInt i oneZ)

LoopO8 :
  (ctx : RawContext) →
  Array63 ctx →
  Int →
  Int →
  Int →
  Int →
  Set
LoopO8 ctx arr2 max1 lenArr i o7 =
  (o8 : Int) →
  In63 o8 →
  LoopO8Condition i o7 o8 max1 →
  (zeroZ ≤Z i ∧ i <Z lengthZ (arrayElts ctx arr2))
  ∧ AllUpdatedArrays ctx arr2 max1 lenArr i o8

DoubleO8Bounds : Int → Set
DoubleO8Bounds i =
  (o8 : Int) →
  In63 o8 →
  o8 ≡ multiplyInt twoZ i →
  In63 (addInt o8 threeZ)

LoopO7 :
  (ctx : RawContext) →
  Array63 ctx →
  Int →
  Int →
  Int →
  Set
LoopO7 ctx arr2 max1 lenArr i =
  (o7 : Int) →
  In63 o7 →
  o7 ≡ subtractInt lenArr oneZ →
  (i ≡ o7 → i ≡ o7) →
  ifSet (intEqual i o7)
    (In63 (addInt max1 oneZ))
    (In63 (multiplyInt twoZ i) ∧ DoubleO8Bounds i)
  ∧ LoopO8 ctx arr2 max1 lenArr i o7

LoopAllI :
  (ctx : RawContext) →
  Array63 ctx →
  Int →
  Int →
  Int →
  Set
LoopAllI ctx arr2 max1 lenArr o6 =
  (i : Int) →
  In63 i →
  (oneZ ≤Z i ∧ i ≤Z o6)
  ∧ PrefixFc1 ctx arr2 max1 lenArr i →
  In63 (subtractInt lenArr oneZ)
  ∧ LoopO7 ctx arr2 max1 lenArr i

AllArr2 :
  (ctx : RawContext) →
  Array63 ctx →
  List Int →
  List Bool →
  Int →
  Int →
  Int →
  Set
AllArr2 ctx arr1 nexts marked max1 lenArr o6 =
  (arr2 : Array63 ctx) →
  arraySize ctx arr2 ≡ arraySize ctx arr1 →
  LoopAllI ctx arr2 max1 lenArr o6
  ∧
  (PrefixFc1 ctx arr2 max1 lenArr (addInt o6 oneZ) →
   PostLoop ctx arr2 nexts marked max1)

AllO6 :
  (ctx : RawContext) →
  Array63 ctx →
  List Int →
  List Bool →
  Int →
  Int →
  Set
AllO6 ctx arr1 nexts marked max1 lenArr =
  (o6 : Int) →
  In63 o6 →
  o6 ≡ subtractInt lenArr oneZ →
  (oneZ ≤Z addInt o6 oneZ →
    PrefixFc1 ctx arr1 max1 lenArr oneZ
    ∧ AllArr2 ctx arr1 nexts marked max1 lenArr o6)
  ∧
  (addInt o6 oneZ <Z oneZ →
    PostLoop ctx arr1 nexts marked max1)

InitialArrayElements :
  (ctx : RawContext) →
  Array63 ctx →
  Int →
  Set
InitialArrayElements ctx arr1 lenArr =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z lenArr →
  nthInt (arrayElts ctx arr1) i ≡ minusTwoZ

AllArr1 :
  (ctx : RawContext) →
  List Int →
  List Bool →
  Int →
  Int →
  Set
AllArr1 ctx nexts marked max1 lenArr =
  (arr1 : Array63 ctx) →
  InitialArrayElements ctx arr1 lenArr
  ∧ lengthZ (arrayElts ctx arr1) ≡ lenArr →
  In63 (subtractInt lenArr oneZ)
  ∧ AllO6 ctx arr1 nexts marked max1 lenArr

NextsCreated : List Int → Int → Int → Set
NextsCreated nexts len max1 =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z len →
  nthInt nexts i ≡ fc max1 i

MarkedCreated : List Bool → Int → Set
MarkedCreated marked len =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z len →
  nthBool marked i ≡ o1 i

NonzeroSideCondition : Set
NonzeroSideCondition =
  (i : Int) →
  i ≠ zeroZ →
  i ≠ oneZ →
  twoZ <Z i →
  twoZ ≠ zeroZ

ListsAndArrays : (ctx : RawContext) → Int → Int → Set
ListsAndArrays ctx max1 lenArr =
  let len = addInt max1 oneZ
      nexts = createList len (fc max1)
      marked = createList len o1
  in
  zeroZ ≤Z len
  ∧
  (lengthZ nexts ≡ len
   ∧ NextsCreated nexts len max1 →
   NonzeroSideCondition
   ∧ zeroZ ≤Z len
   ∧
   (lengthZ marked ≡ len
    ∧ MarkedCreated marked len →
    zeroZ ≤Z lenArr
    ∧ AllArr1 ctx nexts marked max1 lenArr))

AllLenArr : (ctx : RawContext) → Int → Int → Set
AllLenArr ctx max1 o3 =
  (lenArr : Int) →
  In63 lenArr →
  lenArr ≡ addInt o3 oneZ →
  ListsAndArrays ctx max1 lenArr

AllO3 : (ctx : RawContext) → Int → Int → Set
AllO3 ctx max1 o2 =
  (o3 : Int) →
  In63 o3 →
  o3 ≡ tdivTwo o2 →
  In63 (addInt o3 oneZ)
  ∧ AllLenArr ctx max1 o3

AllO2 : (ctx : RawContext) → Int → Set
AllO2 ctx max1 =
  (o2 : Int) →
  In63 o2 →
  o2 ≡ subtractInt max1 oneZ →
  twoZ ≠ zeroZ
  ∧ In63 (tdivTwo o2)
  ∧ AllO3 ctx max1 o2

create'vc : Set₁
create'vc =
  (ctx : RawContext) →
  ContextValid ctx →
  (max1 : Int) →
  In63 max1 →
  max1 <Z max63 →
  threeZ ≤Z max1 →
  In63 (subtractInt max1 oneZ)
  ∧ AllO2 ctx max1
