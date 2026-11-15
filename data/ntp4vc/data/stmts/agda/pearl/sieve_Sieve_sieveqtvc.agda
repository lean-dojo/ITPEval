-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/sieve_Sieve_sieveqtvc: the sieve verification condition whose Boolean
-- list updates and loop invariants establish primality flags over unbounded
-- integers. This file contains no proof.

{-# OPTIONS --safe #-}

module sieve_Sieve_sieveqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤N_ _<N_ _≤Z_ _<Z_
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

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfBool : Bool → Bool → Bool → Bool
IfBool true when-true when-false = when-true
IfBool false when-true when-false = when-false

data _≤N_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤N n
  suc≤suc : {m n : Nat} → m ≤N n → suc m ≤N suc n

_<N_ : Nat → Nat → Set
m <N n = suc m ≤N n

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
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos 1
twoZ = pos 2

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

lengthNat : {A : Set} → List A → Nat
lengthNat [] = zero
lengthNat (_ ∷ xs) = suc (lengthNat xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (lengthNat xs)

nthDefault : {A : Set} → A → List A → Nat → A
nthDefault default [] index = default
nthDefault default (x ∷ xs) zero = x
nthDefault default (x ∷ xs) (suc index) =
  nthDefault default xs index

nthBool : List Bool → Int → Bool
nthBool xs (pos index) = nthDefault false xs index
nthBool xs (negsuc _) = false

setAt : {A : Set} → List A → Nat → A → List A
setAt [] index value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc index) value =
  x ∷ setAt xs index value

setBool : List Bool → Int → Bool → List Bool
setBool xs (pos index) value = setAt xs index value
setBool xs (negsuc _) value = xs

updateBool :
  (Int → Bool) →
  Int →
  Bool →
  Int →
  Bool
updateBool old index value query =
  IfBool (intEqual query index) value (old query)

PointwiseEqual :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
PointwiseEqual f g =
  (x : _) → f x ≡ g x

UpdateCondition :
  List Bool →
  List Bool →
  Int →
  Bool →
  Set →
  Set
UpdateCondition old updated index value conclusion =
  lengthNat updated ≡ lengthNat old →
  PointwiseEqual
    (nthBool updated)
    (updateBool (nthBool old) index value) →
  conclusion

record NatDivides (divisor dividend : Nat) : Set where
  constructor nat-divides
  field
    quotient : Nat
    equation : dividend ≡ divisor * quotient

PrimeNat : Nat → Set
PrimeNat n =
  suc (suc zero) ≤N n
  ∧
  ((divisor : Nat) →
    NatDivides divisor n →
    divisor ≡ suc zero ∨ divisor ≡ n)

PrimeZ : Int → Set
PrimeZ x = PrimeNat (toNat x)

NoFactorLt : Int → Int → Set
NoFactorLt bound number =
  oneZ <Z number
  ∧
  ((k l : Int) →
    ((oneZ <Z l ∧ l <Z bound) ∧ oneZ <Z k) →
    number ≠ multiplyInt k l)

InRange : Int → Int → Set
InRange index n =
  zeroZ ≤Z index ∧ index <Z n

AllTrue : List Bool → Int → Set
AllTrue t n =
  (i : Int) →
  InRange i n →
  nthBool t i ≡ true

SieveInvariant :
  List Bool →
  Int →
  Int →
  Set
SieveInvariant t bound n =
  (j : Int) →
  InRange j n →
  (nthBool t j ≡ true) ↔ NoFactorLt bound j

StrikeInvariant :
  List Bool →
  Int →
  Int →
  Int →
  Set
StrikeInvariant t i r n =
  (j : Int) →
  InRange j n →
  (nthBool t j ≡ true)
  ↔
  (NoFactorLt i j
   ∧
   ((k : Int) →
     oneZ <Z k ∧ k <Z r →
     j ≠ multiplyInt k i))

OuterAdvance :
  List Bool →
  Int →
  Int →
  Set
OuterAdvance t i n =
  (zeroZ ≤Z subtractInt n i
   ∧ subtractInt n (addInt i oneZ)
     <Z subtractInt n i)
  ∧
  (oneZ <Z addInt i oneZ
   ∧ addInt i oneZ ≤Z n)
  ∧ SieveInvariant t (addInt i oneZ) n

InnerAdvance :
  List Bool →
  Int →
  Int →
  Int →
  Set
InnerAdvance updated i r n =
  (zeroZ ≤Z subtractInt n r
   ∧ subtractInt n (addInt r oneZ)
     <Z subtractInt n r)
  ∧
  ((oneZ <Z addInt r oneZ
    ∧ addInt r oneZ ≤Z n)
   ∧ addInt (multiplyInt r i) i
     ≡ multiplyInt (addInt r oneZ) i)
  ∧ StrikeInvariant updated i (addInt r oneZ) n

MarkCompositeBranch :
  List Bool →
  Int →
  Int →
  Int →
  Set
MarkCompositeBranch t i r n =
  let index = multiplyInt r i
      updated = setBool t index false
  in
  (zeroZ ≤Z index ∧ index <Z lengthZ t)
  ∧ UpdateCondition
      t
      updated
      index
      false
      (InnerAdvance updated i r n)

InnerLoopStep :
  List Bool →
  Int →
  Int →
  Int →
  Set
InnerLoopStep t i r n =
  IfSet
    (intLess (multiplyInt r i) n)
    (MarkCompositeBranch t i r n)
    (OuterAdvance t i n)

InnerLoop :
  List Bool →
  Int →
  Int →
  Set
InnerLoop initial i n =
  (r : Int) →
  (t : List Bool) →
  lengthNat t ≡ lengthNat initial →
  ((oneZ <Z r ∧ r ≤Z n)
   ∧ StrikeInvariant t i r n) →
  InnerLoopStep t i r n

PrimeIndexBranch :
  List Bool →
  Int →
  Int →
  Set
PrimeIndexBranch t i n =
  ((oneZ <Z i ∧ i ≤Z n)
   ∧ StrikeInvariant t i i n)
  ∧ InnerLoop t i n

CurrentIndexStep :
  List Bool →
  Int →
  Int →
  Set
CurrentIndexStep t i n =
  (zeroZ ≤Z i ∧ i <Z lengthZ t)
  ∧
  IfSet
    (nthBool t i)
    (PrimeIndexBranch t i n)
    (OuterAdvance t i n)

FinalState :
  List Bool →
  Int →
  Set
FinalState t n =
  lengthZ t ≡ n
  ∧
  ((i : Int) →
    InRange i n →
    (nthBool t i ≡ true) ↔ PrimeZ i)

OuterLoopStep :
  List Bool →
  Int →
  Int →
  Set
OuterLoopStep t i n =
  IfSet
    (intLess i n)
    (CurrentIndexStep t i n)
    (FinalState t n)

OuterLoop :
  List Bool →
  Int →
  Set
OuterLoop initial n =
  (i : Int) →
  (t : List Bool) →
  lengthNat t ≡ lengthNat initial →
  ((oneZ <Z i ∧ i ≤Z n)
   ∧ SieveInvariant t i n) →
  OuterLoopStep t i n

AfterInitialUpdates :
  List Bool →
  Int →
  Set
AfterInitialUpdates t n =
  let after-zero = setBool t zeroZ false
      after-one = setBool after-zero oneZ false
  in
  (zeroZ ≤Z zeroZ ∧ zeroZ <Z lengthZ t)
  ∧ UpdateCondition
      t
      after-zero
      zeroZ
      false
      ((zeroZ ≤Z oneZ ∧ oneZ <Z lengthZ after-zero)
       ∧ UpdateCondition
           after-zero
           after-one
           oneZ
           false
           (((oneZ <Z twoZ ∧ twoZ ≤Z n)
             ∧ SieveInvariant after-one twoZ n)
            ∧ OuterLoop after-one n))

SieveVC : Int → Set
SieveVC n =
  oneZ <Z n →
  zeroZ ≤Z n
  ∧
  ((t : List Bool) →
    (AllTrue t n ∧ lengthZ t ≡ n) →
    AfterInitialUpdates t n)

sieve'vc : Set
sieve'vc =
  (n : Int) →
  SieveVC n
