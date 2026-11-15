-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/euler_sieve_EulerSieve_remove_productsqtvc: the signed 63-bit
-- Euler-sieve verification condition induced by the pinned Why3 source for
-- removing products while preserving the sieve, primality, marking, and
-- successor invariants. This file contains no proof.

{-# OPTIONS --safe #-}

module euler_sieve_EulerSieve_remove_productsqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat
  using (Nat; zero; suc; _+_; _*_; div-helper)

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

record Exists {A : Set} (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

ifSet : Bool → Set → Set → Set
ifSet true A B = A
ifSet false A B = B

ifBool : Bool → Bool → Bool → Bool
ifBool true x y = x
ifBool false x y = y

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

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

-- The pinned Why3 quotient is used here only with nonnegative dividends and
-- positive divisors, where truncation toward zero is the same quotient.
tdivInt : Int → Int → Int
tdivInt (pos _) (pos zero) = pos zero
tdivInt (pos n) (pos (suc m)) = pos (natDivide n (suc m))
tdivInt (pos n) (negsuc m) = negative (natDivide n (suc m))
tdivInt (negsuc _) (pos zero) = pos zero
tdivInt (negsuc n) (pos (suc m)) =
  negative (natDivide (suc n) (suc m))
tdivInt (negsuc n) (negsuc m) =
  pos (natDivide (suc n) (suc m))

modTwoNat : Nat → Nat
modTwoNat zero = zero
modTwoNat (suc zero) = suc zero
modTwoNat (suc (suc n)) = modTwoNat n

-- Euclidean remainder by positive two.
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

NatLE : Nat → Nat → Set
NatLE m n = natLessOrEqual m n ≡ true

record Divides (d n : Nat) : Set where
  constructor divides
  field
    quotient : Nat
    equation : n ≡ d * quotient

PrimeNat : Nat → Set
PrimeNat p =
  NatLE 2 p
  ∧
  ((d : Nat) →
    Divides d p →
    d ≡ 1 ∨ d ≡ p)

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

AllEliminatedMarkedPartial :
  List Bool → List Int → Int → Set
AllEliminatedMarkedPartial marked nexts minimum =
  lengthNat marked ≡ lengthNat nexts
  ∧
  ((i : Int) →
    minimum ≤Z i ∧ i <Z lengthZ marked →
    EliminatedBetween marked nexts i)

NotMarkedImplNextNotMarked :
  List Bool → List Int → Int → Set
NotMarkedImplNextNotMarked marked-old nexts n =
  let bound = tdivInt (subtractInt (lengthZ marked-old) oneZ) n
  in
  lengthNat marked-old ≡ lengthNat nexts
  ∧ twoZ ≤Z lengthZ marked-old
  ∧ twoZ ≤Z n
  ∧
  ((i : Int) →
    twoZ ≤Z i ∧ i ≤Z bound →
    nthInt nexts i ≤Z bound →
    nthBool marked-old i ≠ true →
    nthBool marked-old (nthInt nexts i) ≠ true)

IsCopy : List Bool → List Bool → Set
IsCopy marked marked-old =
  lengthNat marked ≡ lengthNat marked-old
  ∧
  ((i : Int) →
    zeroZ ≤Z i ∧ i <Z lengthZ marked →
    nthBool marked i ≠ true →
    nthBool marked-old i ≠ true)

NotMarkedImplNextNotMarkedPartial :
  List Bool → List Int → Int → Int → Set
NotMarkedImplNextNotMarkedPartial marked nexts n p =
  let bound = tdivInt (subtractInt (lengthZ marked) oneZ) n
  in
  lengthNat marked ≡ lengthNat nexts
  ∧ twoZ ≤Z lengthZ marked
  ∧ twoZ ≤Z n
  ∧ p ≤Z bound
  ∧
  ((i : Int) →
    twoZ ≤Z i ∧ i <Z p →
    nthInt nexts i ≤Z bound →
    nthBool marked i ≠ true →
    nthBool marked (nthInt nexts i) ≠ true)

AllPrimes : List Bool → Int → Set
AllPrimes marked n =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z n →
  (nthBool marked i ≠ true) ↔ PrimeNat (toNat i)

AllMultiplesMarked : List Bool → Int → Int → Set
AllMultiplesMarked marked i maximum =
  (twoZ ≤Z i ∧ i <Z lengthZ marked)
  ∧
  ((k : Int) →
    twoZ ≤Z k ∧ k <Z maximum →
    multiplyInt i k <Z lengthZ marked →
    nthBool marked (multiplyInt i k) ≡ true)

PreviouslyMarkedMultiples : List Bool → Int → Set
PreviouslyMarkedMultiples marked n =
  (i : Int) →
  twoZ ≤Z i ∧ i <Z n →
  AllMultiplesMarked marked i (lengthZ marked)

OnlyMultiplesMarked : List Bool → Int → Set
OnlyMultiplesMarked marked n =
  (k : Int) →
  twoZ ≤Z k ∧ k <Z lengthZ marked →
  nthBool marked k ≡ true →
  Exists λ i →
    Exists λ j →
      (twoZ ≤Z i ∧ i <Z n)
      ∧ (twoZ ≤Z j ∧ j <Z lengthZ marked)
      ∧ multiplyInt i j ≡ k

PrimeMultiplesMarked :
  List Bool → List Bool → Int → Int → Set
PrimeMultiplesMarked marked-old marked n maximum =
  lengthNat marked-old ≡ lengthNat marked
  ∧ (n <Z maximum ∧ maximum ≤Z lengthZ marked)
  ∧
  ((i : Int) →
    n ≤Z i ∧ i <Z maximum →
    nthBool marked-old i ≠ true →
    multiplyInt n i <Z lengthZ marked-old →
    nthBool marked (multiplyInt n i) ≡ true)

InvRemoveProducts : List Int → List Bool → Int → Set
InvRemoveProducts nexts marked n =
  lengthNat nexts ≡ lengthNat marked
  ∧ nthBool marked twoZ ≠ true
  ∧ AllPrimes marked n
  ∧ PrimeNat (toNat n)
  ∧ nthBool marked n ≠ true
  ∧ InvNexts nexts (lengthZ nexts)

record RawContext : Set₁ where
  field
    State        : Set
    defaultState : State
    nexts        : State → List Int
    marked       : State → List Bool
    maximum      : State → Int

open RawContext

StateInvariant : (ctx : RawContext) → State ctx → Set
StateInvariant ctx self =
  let ns = nexts ctx self
      ms = marked ctx self
      mx = maximum ctx self
  in
  mx <Z max63
  ∧ threeZ ≤Z mx
  ∧ lengthNat ns ≡ lengthNat ms
  ∧ lengthZ ms ≡ addInt mx oneZ
  ∧ InvNexts ns (lengthZ ns)
  ∧ AllEliminatedMarked ms ns
  ∧
    ((i : Int) →
      threeZ ≤Z i ∧ i ≤Z mx →
      emodTwo i ≡ zeroZ →
      nthBool ms i ≡ true)
  ∧
    ((i : Int) →
      threeZ ≤Z i ∧ i <Z subtractInt mx oneZ →
      emodTwo i ≡ oneZ →
      emodTwo (nthInt ns i) ≡ oneZ
      ∨ nthInt ns i ≡ addInt mx oneZ)
  ∧ nthInt ns mx ≡ addInt mx oneZ
  ∧
    (emodTwo (subtractInt mx oneZ) ≡ zeroZ →
     nthInt ns (subtractInt mx oneZ) ≡ mx)
  ∧
    (emodTwo (subtractInt mx oneZ) ≡ oneZ →
     nthInt ns (subtractInt mx oneZ) ≡ addInt mx oneZ)

ContextValid : RawContext → Set
ContextValid ctx =
  ((self : State ctx) → In63 (maximum ctx self))
  ∧ ((self : State ctx) → StateInvariant ctx self)

LoopInvariant :
  (ctx : RawContext) →
  Int → Int → List Bool →
  State ctx → Int → Int → Set
LoopInvariant ctx n max1 marked-old t p x =
  let ns = nexts ctx t
      ms = marked ctx t
  in
  ((n ≤Z p ∧ p ≤Z max1)
   ∧ (threeZ ≤Z n ∧ n ≤Z max1)
   ∧ emodTwo p ≡ oneZ
   ∧ (p ≤Z x ∧ x <Z nthInt ns p)
   ∧ nthInt ns x ≡ nthInt ns p
   ∧ nthBool ms (multiplyInt n n) ≡ true)
  ∧ InvRemoveProducts ns ms n
  ∧ PreviouslyMarkedMultiples ms n
  ∧ nthBool ms p ≠ true
  ∧ IsCopy ms marked-old
  ∧ AllEliminatedMarkedPartial marked-old ns x
  ∧ NotMarkedImplNextNotMarked marked-old ns n
  ∧ PrimeMultiplesMarked marked-old ms n (nthInt ns x)
  ∧ NotMarkedImplNextNotMarkedPartial ms ns n p
  ∧ OnlyMultiplesMarked ms (addInt n oneZ)

FinalState :
  (ctx : RawContext) →
  Int → List Bool → State ctx → Set
FinalState ctx n marked-old t =
  let ns = nexts ctx t
      ms = marked ctx t
  in
  InvRemoveProducts ns ms n
  ∧ NotMarkedImplNextNotMarked ms ns (nthInt ns n)
  ∧ IsCopy ms marked-old
  ∧ PreviouslyMarkedMultiples ms n
  ∧ PrimeMultiplesMarked marked-old ms n (lengthZ ms)
  ∧ OnlyMultiplesMarked ms (addInt n oneZ)

FinalConclusion :
  (ctx : RawContext) →
  Int → State ctx → Set
FinalConclusion ctx n t =
  let ns = nexts ctx t
      ms = marked ctx t
      nextn = nthInt ns n
  in
  InvRemoveProducts ns ms n
  ∧ NotMarkedImplNextNotMarked ms ns nextn
  ∧ PreviouslyMarkedMultiples ms nextn
  ∧ OnlyMultiplesMarked ms nextn

NextCondition :
  (ctx : RawContext) →
  State ctx → Int → Int → Set
NextCondition ctx t p next =
  let ns = nexts ctx t
      mx = maximum ctx t
  in
  (threeZ ≤Z next ∧ next ≤Z addInt mx oneZ)
  ∧ next ≡ nthInt ns p
  ∧ (emodTwo next ≡ oneZ ∨ next ≡ addInt mx oneZ)

O2Condition :
  (ctx : RawContext) →
  State ctx → Int → Bool → Set
O2Condition ctx t next o2 =
  let mx = maximum ctx t
  in
  ifSet (intLessOrEqual zeroZ next)
    (twoZ ≤Z mx
     ∧ o2 ≡ ifBool (intLessOrEqual next mx) true false)
    (o2 ≡ false)

NextUpdateFacts :
  (ctx : RawContext) →
  State ctx → Int → Int → Set
NextUpdateFacts ctx t p o4 =
  let ms = marked ctx t
      mx = maximum ctx t
  in
  (((zeroZ ≤Z p ∧ p ≤Z mx)
    ∧ p <Z o4
    ∧ o4 ≤Z addInt mx oneZ)
   ∧ emodTwo p ≡ oneZ
   ∧
     ((j : Int) →
       p <Z j ∧ j <Z o4 →
       nthBool ms j ≡ true)
   ∧ nthBool ms p ≠ true
   ∧ (emodTwo o4 ≡ oneZ ∨ o4 ≡ addInt mx oneZ))

UpdatedSuccessorBranch :
  (ctx : RawContext) →
  Int → Int → List Bool →
  State ctx → Int → Int → State ctx → Int → Set
UpdatedSuccessorBranch ctx n max1 marked-old t2 p next t3 o4 =
  NextUpdateFacts ctx t3 p o4
  ∧
  ((t4 : State ctx) →
    marked ctx t4 ≡ marked ctx t3
      ∧ maximum ctx t4 ≡ maximum ctx t3 →
    nexts ctx t4 ≡ setList (nexts ctx t3) p o4 →
    (zeroZ ≤Z
       subtractInt max1 (nthInt (nexts ctx t2) p)
     ∧
    subtractInt max1 (nthInt (nexts ctx t4) p)
       <Z subtractInt max1 (nthInt (nexts ctx t2) p))
    ∧ LoopInvariant ctx n max1 marked-old t4 p next)

MarkedNextBranch :
  (ctx : RawContext) →
  Int → Int → List Bool →
  State ctx → Int → Int → State ctx → Set
MarkedNextBranch ctx n max1 marked-old t2 p next t3 =
  ((threeZ ≤Z next ∧ next ≤Z maximum ctx t3)
   ∧ emodTwo next ≡ oneZ)
  ∧
  ((o4 : Int) →
    In63 o4 →
    ((threeZ ≤Z o4
      ∧ o4 ≤Z addInt (maximum ctx t3) oneZ)
     ∧ o4 ≡ nthInt (nexts ctx t3) next
     ∧
       (emodTwo o4 ≡ oneZ
        ∨ o4 ≡ addInt (maximum ctx t3) oneZ)) →
    UpdatedSuccessorBranch
      ctx n max1 marked-old t2 p next t3 o4)

UnmarkedNextBranch :
  (ctx : RawContext) →
  Int → Int → List Bool →
  State ctx → Int → State ctx → Int → Set
UnmarkedNextBranch ctx n max1 marked-old t2 p t3 next =
  (zeroZ ≤Z
     subtractInt max1 (nthInt (nexts ctx t2) p)
   ∧
   subtractInt max1 (nthInt (nexts ctx t3) next)
     <Z subtractInt max1 (nthInt (nexts ctx t2) p))
  ∧ LoopInvariant ctx n max1 marked-old t3 next next

AfterProductWrite :
  (ctx : RawContext) →
  Int → Int → List Bool →
  State ctx → Int → Int → Int → State ctx → Set
AfterProductWrite ctx n max1 marked-old t2 p next o3 t3 =
  ((zeroZ ≤Z next ∧ next ≤Z maximum ctx t3)
   ∧ emodTwo next ≡ oneZ)
  ∧
  ifSet (nthBool (marked ctx t3) next)
    (MarkedNextBranch ctx n max1 marked-old t2 p next t3)
    (UnmarkedNextBranch ctx n max1 marked-old t2 p t3 next)

ProductResult :
  (ctx : RawContext) →
  Int → Int → List Bool →
  State ctx → Int → Int → Int → Set
ProductResult ctx n max1 marked-old t2 p next o3 =
  ((zeroZ ≤Z o3 ∧ o3 ≤Z maximum ctx t2)
   ∧ emodTwo o3 ≡ oneZ)
  ∧
  ((t3 : State ctx) →
    (nexts ctx t3 ≡ nexts ctx t2
     ∧ maximum ctx t3 ≡ maximum ctx t2) →
    marked ctx t3 ≡ setList (marked ctx t2) o3 true →
    AfterProductWrite
      ctx n max1 marked-old t2 p next o3 t3)

ProductPath :
  (ctx : RawContext) →
  Int → Int → List Bool →
  State ctx → Int → Int → Set
ProductPath ctx n max1 marked-old t2 p next =
  In63 (multiplyInt n next)
  ∧
  ((o3 : Int) →
    In63 o3 →
    o3 ≡ multiplyInt n next →
    ProductResult ctx n max1 marked-old t2 p next o3)

LoopStep :
  (ctx : RawContext) →
  Int → Int → Int → List Bool →
  State ctx → Int → Int → Set
LoopStep ctx n d max1 marked-old t2 p next =
  (o2 : Bool) →
  O2Condition ctx t2 next o2 →
  ifSet o2
    (ifSet (intLessOrEqual next d)
      (ProductPath ctx n max1 marked-old t2 p next)
      (FinalState ctx n marked-old t2))
    (FinalState ctx n marked-old t2)

LoopBody :
  (ctx : RawContext) →
  Int → Int → Int → List Bool →
  State ctx → Int → Int → Set
LoopBody ctx n d max1 marked-old t2 p x =
  ((threeZ ≤Z p ∧ p ≤Z maximum ctx t2)
   ∧ emodTwo p ≡ oneZ)
  ∧
  ((next : Int) →
    In63 next →
    NextCondition ctx t2 p next →
    LoopStep ctx n d max1 marked-old t2 p next)

AllLoopObligations :
  (ctx : RawContext) →
  Int → Int → Int → List Bool → State ctx → Set
AllLoopObligations ctx n d max1 marked-old t1 =
  (t2 : State ctx) →
  maximum ctx t2 ≡ maximum ctx t1 →
  (p : Int) →
  In63 p →
  (x : Int) →
  LoopInvariant ctx n max1 marked-old t2 p x →
  LoopBody ctx n d max1 marked-old t2 p x

SquareContinuation :
  (ctx : RawContext) →
  Int → Int → List Bool →
  State ctx → Int → State ctx → Set
SquareContinuation ctx n max1 marked-old t1 o2 t2 =
  LoopInvariant ctx n max1 marked-old t2 n n
  ∧
  ((t3 : State ctx) →
    maximum ctx t3 ≡ maximum ctx t2 →
    FinalState ctx n marked-old t3 →
    FinalConclusion ctx n t3)

SquareResult :
  (ctx : RawContext) →
  Int → Int → List Bool →
  State ctx → Int → Set
SquareResult ctx n max1 marked-old t1 o2 =
  ((zeroZ ≤Z o2 ∧ o2 ≤Z maximum ctx t1)
   ∧ emodTwo o2 ≡ oneZ)
  ∧
  ((t2 : State ctx) →
    (nexts ctx t2 ≡ nexts ctx t1
     ∧ maximum ctx t2 ≡ maximum ctx t1) →
    marked ctx t2 ≡ setList (marked ctx t1) o2 true →
    SquareContinuation ctx n max1 marked-old t1 o2 t2)

SquareObligations :
  (ctx : RawContext) →
  Int → Int → List Bool → State ctx → Set
SquareObligations ctx n max1 marked-old t1 =
  In63 (multiplyInt n n)
  ∧
  ((o2 : Int) →
    In63 o2 →
    o2 ≡ multiplyInt n n →
    SquareResult ctx n max1 marked-old t1 o2)

RemoveProductsResult :
  (ctx : RawContext) →
  Int → Int → State ctx → Set
RemoveProductsResult ctx n d t1 =
  let max1 = maximum ctx t1
      marked-old = marked ctx t1
  in
  AllLoopObligations ctx n d max1 marked-old t1
  ∧ SquareObligations ctx n max1 marked-old t1

remove-products-vc : Set₁
remove-products-vc =
  (ctx : RawContext) →
  ContextValid ctx →
  (n : Int) →
  In63 n →
  (t1 : State ctx) →
  threeZ ≤Z n →
  n ≤Z maximum ctx t1 →
  multiplyInt n n ≤Z maximum ctx t1 →
  InvRemoveProducts (nexts ctx t1) (marked ctx t1) n →
  PreviouslyMarkedMultiples (marked ctx t1) n →
  OnlyMultiplesMarked (marked ctx t1) n →
  NotMarkedImplNextNotMarked
    (marked ctx t1) (nexts ctx t1) n →
  twoZ ≤Z maximum ctx t1 →
  (n ≠ zeroZ
   ∧ In63 (tdivInt (maximum ctx t1) n))
  ∧
  ((d : Int) →
    In63 d →
    d ≡ tdivInt (maximum ctx t1) n →
    RemoveProductsResult ctx n d t1)
