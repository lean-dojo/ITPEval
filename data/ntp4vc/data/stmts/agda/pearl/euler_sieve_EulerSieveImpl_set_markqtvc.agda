-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/euler_sieve_EulerSieveImpl_set_markqtvc: the signed 63-bit
-- Euler-sieve verification condition for marking an odd index and updating
-- its compressed array while preserving the state invariants. This file contains no proof.

{-# OPTIONS --safe #-}

module euler_sieve_EulerSieveImpl_set_markqtvc where

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

ifSet : Bool → Set → Set → Set
ifSet true A B = A
ifSet false A B = B

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

-- Truncation toward zero, matching signed machine-integer division.
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

max63 min63 : Int
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

record RawContext : Set₁ where
  field
    Array63 State : Set
    arrayElts : Array63 → List Int
    arraySize : Array63 → Int
    stateNexts : State → List Int
    stateMarked : State → List Bool
    stateArr : State → Array63
    stateMax : State → Int
    stateMaxArr : State → Int

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
  lengthNat marked ≡ lengthNat nexts
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

StateInvariantIndex : (ctx : RawContext) → State ctx → Set
StateInvariantIndex ctx self =
  let marked = stateMarked ctx self
      nexts = stateNexts ctx self
      els = arrayElts ctx (stateArr ctx self)
      maximum = stateMax ctx self
      maximumArr = stateMaxArr ctx self
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

StateInvariant : (ctx : RawContext) → State ctx → Set
StateInvariant ctx self =
  let marked = stateMarked ctx self
      nexts = stateNexts ctx self
      els = arrayElts ctx (stateArr ctx self)
      maximum = stateMax ctx self
      maximumArr = stateMaxArr ctx self
  in
  maximum <Z max63
  ∧ threeZ ≤Z maximum
  ∧ lengthNat nexts ≡ lengthNat marked
  ∧ lengthZ marked ≡ addInt maximum oneZ
  ∧ edivTwo (subtractInt maximum oneZ) ≡ maximumArr
  ∧ lengthZ els ≡ addInt maximumArr oneZ
  ∧ InvNexts nexts (lengthZ nexts)
  ∧ AllEliminatedMarked marked nexts
  ∧ StateInvariantIndex ctx self
  ∧ nthInt nexts maximum ≡ addInt maximum oneZ
  ∧
    (emodTwo (subtractInt maximum oneZ) ≡ zeroZ →
     nthInt nexts (subtractInt maximum oneZ) ≡ maximum)
  ∧
    (emodTwo (subtractInt maximum oneZ) ≡ oneZ →
     nthInt nexts (subtractInt maximum oneZ)
       ≡ addInt maximum oneZ)

StateFieldsEqual : (ctx : RawContext) → State ctx → State ctx → Set
StateFieldsEqual ctx a b =
  stateNexts ctx a ≡ stateNexts ctx b
  ∧ stateMarked ctx a ≡ stateMarked ctx b
  ∧ stateArr ctx a ≡ stateArr ctx b
  ∧ stateMax ctx a ≡ stateMax ctx b
  ∧ stateMaxArr ctx a ≡ stateMaxArr ctx b

ContextValid : RawContext → Set
ContextValid ctx =
  ((a : Array63 ctx) → ArrayInvariant ctx a)
  ∧ ((self : State ctx) → In63 (stateMax ctx self))
  ∧ ((self : State ctx) → In63 (stateMaxArr ctx self))
  ∧ ((self : State ctx) → StateInvariant ctx self)
  ∧
  ((a b : State ctx) →
    StateFieldsEqual ctx a b →
    a ≡ b)

UpdatedInvariantIndex :
  (ctx : RawContext) →
  State ctx →
  Array63 ctx →
  List Bool →
  Set
UpdatedInvariantIndex ctx t1 tArr marked =
  let nexts = stateNexts ctx t1
      els = arrayElts ctx tArr
      maximum = stateMax ctx t1
      maximumArr = stateMaxArr ctx t1
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

UpdatedInvariant :
  (ctx : RawContext) →
  State ctx →
  Array63 ctx →
  List Bool →
  Set
UpdatedInvariant ctx t1 tArr marked =
  let nexts = stateNexts ctx t1
      maximum = stateMax ctx t1
      maximumArr = stateMaxArr ctx t1
  in
  (maximum <Z max63 ∧ threeZ ≤Z maximum)
  ∧
  (lengthNat nexts ≡ lengthNat marked
   ∧ lengthZ marked ≡ addInt maximum oneZ)
  ∧ edivTwo (subtractInt maximum oneZ) ≡ maximumArr
  ∧ lengthZ (arrayElts ctx tArr) ≡ addInt maximumArr oneZ
  ∧ InvNexts nexts (lengthZ nexts)
  ∧ AllEliminatedMarked marked nexts
  ∧
    (nthInt nexts maximum ≡ addInt maximum oneZ
     ∧
     (emodTwo (subtractInt maximum oneZ) ≡ zeroZ →
      nthInt nexts (subtractInt maximum oneZ) ≡ maximum)
     ∧
     (emodTwo (subtractInt maximum oneZ) ≡ oneZ →
      nthInt nexts (subtractInt maximum oneZ)
        ≡ addInt maximum oneZ))
  ∧ UpdatedInvariantIndex ctx t1 tArr marked

UpdatedStateConclusion :
  (ctx : RawContext) →
  State ctx →
  Array63 ctx →
  List Bool →
  Int →
  State ctx →
  Set
UpdatedStateConclusion ctx t1 tArr marked i t2 =
  UpdatedInvariant ctx t1 tArr marked
  ∧
  (stateMaxArr ctx t1 ≡ stateMaxArr ctx t2
   ∧ stateMax ctx t1 ≡ stateMax ctx t2
   ∧ tArr ≡ stateArr ctx t2
   ∧ marked ≡ stateMarked ctx t2
   ∧ stateNexts ctx t1 ≡ stateNexts ctx t2 →
   stateMarked ctx t2 ≡ setList (stateMarked ctx t1) i true)

AllUpdatedStates :
  (ctx : RawContext) →
  State ctx →
  Array63 ctx →
  List Bool →
  Int →
  Set
AllUpdatedStates ctx t1 tArr marked i =
  (t2 : State ctx) →
  UpdatedStateConclusion ctx t1 tArr marked i t2

ListUpdateProperties :
  List Bool →
  List Bool →
  Int →
  Bool →
  Set
ListUpdateProperties old updated index value =
  lengthNat updated ≡ lengthNat old
  ∧ nthBool updated index ≡ value
  ∧
  ((j : Int) →
    (zeroZ ≤Z j ∧ j <Z lengthZ old)
    ∧ j ≠ index →
    nthBool updated j ≡ nthBool old j)

MarkUpdate :
  (ctx : RawContext) →
  State ctx →
  Array63 ctx →
  Int →
  Set
MarkUpdate ctx t1 tArr i =
  let old = stateMarked ctx t1
      updated = setList old i true
  in
  (zeroZ ≤Z i ∧ i <Z lengthZ old)
  ∧
  (ListUpdateProperties old updated i true →
   AllUpdatedStates ctx t1 tArr updated i)

PositiveEntryBranch :
  (ctx : RawContext) →
  State ctx →
  Int →
  Int →
  Set
PositiveEntryBranch ctx t1 i x =
  (zeroZ ≤Z x ∧ x <Z lengthZ (arrayElts ctx (stateArr ctx t1)))
  ∧
  ((o4 : Int) →
    In63 o4 →
    o4 ≡ nthInt (arrayElts ctx (stateArr ctx t1)) x →
    In63 (negateInt o4)
    ∧
    ((o5 : Int) →
      In63 o5 →
      o5 ≡ negateInt o4 →
      (zeroZ ≤Z x
       ∧ x <Z lengthZ (arrayElts ctx (stateArr ctx t1)))
      ∧
      ((tArr : Array63 ctx) →
        arraySize ctx tArr ≡ arraySize ctx (stateArr ctx t1) →
        arraySize ctx tArr ≡ arraySize ctx (stateArr ctx t1) →
        arrayElts ctx tArr ≡
          setList (arrayElts ctx (stateArr ctx t1)) x o5 →
        MarkUpdate ctx t1 tArr i)))

EntryBranch :
  (ctx : RawContext) →
  State ctx →
  Int →
  Int →
  Int →
  Set
EntryBranch ctx t1 i x o2 =
  ifSet (intLessOrEqual zeroZ o2)
    (PositiveEntryBranch ctx t1 i x)
    (MarkUpdate ctx t1 (stateArr ctx t1) i)

AllEntries :
  (ctx : RawContext) →
  State ctx →
  Int →
  Int →
  Set
AllEntries ctx t1 i x =
  (o2 : Int) →
  In63 o2 →
  o2 ≡ nthInt (arrayElts ctx (stateArr ctx t1)) x →
  EntryBranch ctx t1 i x o2

AllCompressedIndices :
  (ctx : RawContext) →
  State ctx →
  Int →
  Set
AllCompressedIndices ctx t1 i =
  (x : Int) →
  In63 x →
  x ≡ tdivTwo i →
  (zeroZ ≤Z x ∧ x <Z lengthZ (arrayElts ctx (stateArr ctx t1)))
  ∧ AllEntries ctx t1 i x

set-mark-vc : Set₁
set-mark-vc =
  (ctx : RawContext) →
  ContextValid ctx →
  (i : Int) →
  In63 i →
  (t1 : State ctx) →
  zeroZ ≤Z i →
  i ≤Z stateMax ctx t1 →
  emodTwo i ≡ oneZ →
  twoZ ≠ zeroZ
  ∧ In63 (tdivTwo i)
  ∧ AllCompressedIndices ctx t1 i
