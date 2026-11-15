-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/knuth_prime_numbers_PrimeNumbers_prime_numbersqtvc: the integer-array
-- verification condition for constructing the first prime numbers by testing
-- successive odd candidates. This file contains no proof.

{-# OPTIONS --safe #-}

module knuth_prime_numbers_PrimeNumbers_prime_numbersqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat
  using (Nat; zero; suc; _+_; _*_; div-helper)

infix 4 _≠_ _≤N_ _<N_ _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

ifNat : Bool → Nat → Nat → Nat
ifNat true x y = x
ifNat false x y = y

natModFuel : Nat → Nat → Nat → Nat
natModFuel zero dividend divisor = dividend
natModFuel (suc fuel) dividend zero = dividend
natModFuel (suc fuel) dividend (suc divisor) =
  ifNat
    (natLess dividend (suc divisor))
    dividend
    (natModFuel fuel
      (natSubtract dividend (suc divisor))
      (suc divisor))

natMod : Nat → Nat → Nat
natMod dividend divisor =
  natModFuel (suc dividend) dividend divisor

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

absoluteNat : Int → Nat
absoluteNat (pos n) = n
absoluteNat (negsuc n) = suc n

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

-- Signed quotient truncated toward zero, matching Int.tdiv and cdiv.
tdivInt : Int → Int → Int
tdivInt (pos _) (pos zero) = pos zero
tdivInt (pos n) (pos (suc m)) = pos (natDivide n (suc m))
tdivInt (pos n) (negsuc m) = negative (natDivide n (suc m))
tdivInt (negsuc _) (pos zero) = pos zero
tdivInt (negsuc n) (pos (suc m)) =
  negative (natDivide (suc n) (suc m))
tdivInt (negsuc n) (negsuc m) =
  pos (natDivide (suc n) (suc m))

-- Signed remainder with the dividend's sign, matching Int.tmod and cmod.
tmodInt : Int → Int → Int
tmodInt (pos n) divisor =
  pos (natMod n (absoluteNat divisor))
tmodInt (negsuc n) divisor =
  negative (natMod (suc n) (absoluteNat divisor))

zeroZ oneZ twoZ threeZ fiveZ : Int
zeroZ = pos zero
oneZ = pos 1
twoZ = pos 2
threeZ = pos 3
fiveZ = pos 5

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

updateInt : (Int → Int) → Int → Int → Int → Int
updateInt f index value argument =
  ifInt (intEqual argument index) value (f argument)

record ArrayState : Set where
  constructor array-state
  field
    arrayLength : Int
    arrayElts   : Int → Int

open ArrayState

lengthZ : ArrayState → Int
lengthZ = arrayLength

nthInt : ArrayState → Int → Int
nthInt = arrayElts

setArray : ArrayState → Int → Int → ArrayState
setArray p index value =
  array-state
    (arrayLength p)
    (updateInt (arrayElts p) index value)

FunctionEqual : (Int → Int) → (Int → Int) → Set
FunctionEqual f g = (x : Int) → f x ≡ g x

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

IntDivides : Int → Int → Set
IntDivides divisor dividend =
  Exists Int
    (λ quotient →
      dividend ≡ multiplyInt divisor quotient)

OddZ : Int → Set
OddZ n =
  Exists Int
    (λ k →
      n ≡ addInt (multiplyInt twoZ k) oneZ)

NoPrimeIn : Int → Int → Set
NoPrimeIn lower upper =
  (x : Int) →
  lower <Z x ∧ x <Z upper →
  Not (PrimeZ x)

FirstPrimes : (Int → Int) → Int → Set
FirstPrimes p upper =
  p zeroZ ≡ twoZ
  ∧
  ((i j : Int) →
    zeroZ ≤Z i ∧ i <Z j ∧ j <Z upper →
    p i <Z p j)
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i <Z upper →
    PrimeZ (p i))
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i <Z subtractInt upper oneZ →
    NoPrimeIn (p i) (p (addInt i oneZ)))

BertrandPostulate : Set
BertrandPostulate =
  (p : Int) →
  PrimeZ p →
  Not (NoPrimeIn p (multiplyInt twoZ p))

IndexBound : ArrayState → Int → Set
IndexBound p i =
  zeroZ ≤Z i ∧ i <Z lengthZ p

LastValue : ArrayState → Int → Int
LastValue p j =
  nthInt p (subtractInt j oneZ)

CandidateRange : ArrayState → Int → Int → Set
CandidateRange p j n =
  LastValue p j <Z n
  ∧ n <Z multiplyInt twoZ (LastValue p j)

SearchState : ArrayState → Int → Int → Set
SearchState p j n =
  FirstPrimes (nthInt p) j
  ∧ CandidateRange p j n
  ∧ OddZ n
  ∧ NoPrimeIn (LastValue p j) n

NoDivisorBefore : ArrayState → Int → Int → Set
NoDivisorBefore p upper n =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z upper →
  Not (IntDivides (nthInt p i) n)

JInvariant : ArrayState → Int → Int → Int → Set
JInvariant p j n o1 =
  (twoZ ≤Z j ∧ j ≤Z o1)
  ∧ SearchState p j n

KInvariant : ArrayState → Int → Int → Int → Set
KInvariant p j n k =
  (oneZ ≤Z k ∧ k <Z j)
  ∧ SearchState p j n
  ∧ NoDivisorBefore p k n

CandidatePrime : ArrayState → Int → Int → Set
CandidatePrime p j n =
  LastValue p j <Z n
  ∧ PrimeZ n
  ∧ NoPrimeIn (LastValue p j) n

ResetState : ArrayState → Int → Int → Set
ResetState p j n =
  (oneZ ≤Z oneZ ∧ oneZ <Z j)
  ∧ SearchState p j n
  ∧ NoDivisorBefore p oneZ n

DivisibleDecrease : ArrayState → Int → Int → Int → Set
DivisibleDecrease p j n k =
  let distance = subtractInt
        (multiplyInt twoZ (LastValue p j))
        n
      nextDistance = subtractInt
        (multiplyInt twoZ (LastValue p j))
        (addInt n twoZ)
  in
  (zeroZ ≤Z distance ∧ nextDistance <Z distance)
  ∨
  (distance ≡ nextDistance
   ∧ zeroZ ≤Z subtractInt j k
   ∧ subtractInt j oneZ <Z subtractInt j k)

AdvanceDecrease : ArrayState → Int → Int → Int → Set
AdvanceDecrease p j n k =
  let distance = subtractInt
        (multiplyInt twoZ (LastValue p j))
        n
      o4 = addInt k oneZ
  in
  (zeroZ ≤Z distance ∧ distance <Z distance)
  ∨
  (zeroZ ≤Z subtractInt j k
   ∧ subtractInt j o4 <Z subtractInt j k)

DivisibleBranch : ArrayState → Int → Int → Int → Set
DivisibleBranch p j n k =
  DivisibleDecrease p j n k
  ∧ ResetState p j (addInt n twoZ)

AdvanceBranch : ArrayState → Int → Int → Int → Set
AdvanceBranch p j n k =
  let o4 = addInt k oneZ
  in
  AdvanceDecrease p j n k
  ∧
  ((oneZ ≤Z o4 ∧ o4 <Z j)
   ∧ SearchState p j n
   ∧ NoDivisorBefore p o4 n)

NondivisibleBranch : ArrayState → Int → Int → Int → Set
NondivisibleBranch p j n k =
  IndexBound p k
  ∧ IndexBound p k
  ∧
  (let o3 = nthInt p k
   in
   o3 ≠ zeroZ
   ∧
   ifSet
     (intLess (nthInt p k) (tdivInt n o3))
     (AdvanceBranch p j n k)
     (CandidatePrime p j n))

KBranch : ArrayState → Int → Int → Int → Set
KBranch p j n k =
  let o2 = nthInt p k
  in
  o2 ≠ zeroZ
  ∧
  ifSet
    (intEqual (tmodInt n o2) zeroZ)
    (DivisibleBranch p j n k)
    (NondivisibleBranch p j n k)

KLoop : ArrayState → Int → Int → Set
KLoop p j n =
  (k : Int) →
  KInvariant p j n k →
  IndexBound p k
  ∧ KBranch p j n k

AllKLoops : ArrayState → Int → Int → Set
AllKLoops p1 j n =
  (n1 : Int) →
  (p2 : ArrayState) →
  lengthZ p2 ≡ lengthZ p1 →
  KLoop p2 j n1

SetPreservesModel : ArrayState → Int → Int → Set
SetPreservesModel p index value =
  lengthZ (setArray p index value) ≡ lengthZ p
  ∧
  FunctionEqual
    (nthInt (setArray p index value))
    (updateInt (nthInt p) index value)

CandidateInsertion : ArrayState → Int → Set
CandidateInsertion p j =
  (n1 : Int) →
  CandidatePrime p j n1 →
  IndexBound p j
  ∧
  (SetPreservesModel p j n1 →
   SearchState
     (setArray p j n1)
     (addInt j oneZ)
     (addInt n1 twoZ))

JStep : ArrayState → Int → Int → Set
JStep p j n =
  AllKLoops p j n
  ∧ ResetState p j n
  ∧ CandidateInsertion p j

FinalLoopState : ArrayState → Int → Int → Set
FinalLoopState p upper n =
  SearchState p upper n

AllJSteps : ArrayState → Int → Int → Set
AllJSteps prepared m o1 =
  (n : Int) →
  (p1 : ArrayState) →
  lengthZ p1 ≡ lengthZ prepared →
  (((j : Int) →
      JInvariant p1 j n o1 →
      JStep p1 j n)
   ∧
   (FinalLoopState p1 (addInt o1 oneZ) n →
    lengthZ p1 ≡ m
    ∧ FirstPrimes (nthInt p1) m))

MainBranch : ArrayState → Int → Int → Set
MainBranch prepared m o1 =
  SearchState prepared twoZ fiveZ
  ∧ AllJSteps prepared m o1

SmallBranch : ArrayState → Int → Set
SmallBranch prepared m =
  lengthZ prepared ≡ m
  ∧ FirstPrimes (nthInt prepared) m

PreparedBranches : ArrayState → Int → Set
PreparedBranches prepared m =
  let o1 = subtractInt m oneZ
  in
  (twoZ ≤Z addInt o1 oneZ →
   MainBranch prepared m o1)
  ∧
  (addInt o1 oneZ <Z twoZ →
   SmallBranch prepared m)

AfterFirstSet : ArrayState → Int → Set
AfterFirstSet p m =
  let p0 = setArray p zeroZ twoZ
      prepared = setArray p0 oneZ threeZ
  in
  IndexBound p0 oneZ
  ∧
  (SetPreservesModel p0 oneZ threeZ →
   PreparedBranches prepared m)

InitializeArray : ArrayState → Int → Set
InitializeArray p m =
  IndexBound p zeroZ
  ∧
  (SetPreservesModel p zeroZ twoZ →
   AfterFirstSet p m)

InitialZeroArray : ArrayState → Int → Set
InitialZeroArray p m =
  ((i : Int) →
    zeroZ ≤Z i ∧ i <Z m →
    nthInt p i ≡ zeroZ)
  ∧ lengthZ p ≡ m

PrimeNumbersBody : Int → Set
PrimeNumbersBody m =
  zeroZ ≤Z m
  ∧
  ((p : ArrayState) →
    InitialZeroArray p m →
    InitializeArray p m)

prime-numbers-vc : Set
prime-numbers-vc =
  BertrandPostulate →
  (m : Int) →
  twoZ ≤Z m →
  PrimeNumbersBody m
