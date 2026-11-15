-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/search_Bfs_bfsqtvc: the breadth-first-search verification condition
-- for layer invariants, successor collection, successful termination, and
-- exhaustion without a reachable successful state. This file contains no proof.

{-# OPTIONS --safe #-}

module search_Bfs_bfsqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

data Member {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → Member x (x ∷ xs)
  there : {y : A} {xs : List A} → Member x xs → Member x (y ∷ xs)

module SearchTheory
  (State : Set)
  (defaultState : State)
  (moves : State → List State)
  (start : State)
  (success : State → Set)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  where

  decide : (P : Set) → Dec P
  decide P with excludedMiddle P
  ... | left proof = yes proof
  ... | right refutation = no refutation

  IfDec : {P : Set} → Dec P → Set → Set → Set
  IfDec (yes _) when-true when-false = when-true
  IfDec (no _) when-true when-false = when-false

  IfProp : (P : Set) → Set → Set → Set
  IfProp P when-true when-false =
    IfDec (decide P) when-true when-false

  nthState : List State → Int → State
  nthState xs index =
    nthDefault defaultState (toNat index) xs

  data Path : State → State → Int → Set where
    path-zero :
      (s : State) →
      Path s s zeroZ

    path-one :
      (i : Int) →
      (s : State) →
      (zeroZ ≤Z i ∧ i <Z lengthZ (moves s)) →
      Path s (nthState (moves s) i) oneZ

    path-transitive :
      (s t u : State) →
      (n m : Int) →
      Path s t n →
      Path t u m →
      Path s u (addInt n m)

  Move : State → State → Set
  Move s t =
    Exists Int λ i →
      (zeroZ ≤Z i ∧ i <Z lengthZ (moves s)) ∧
      t ≡ nthState (moves s) i

  AllAtLayer : Int → List State → Set
  AllAtLayer p cur =
    (i : Int) →
    (zeroZ ≤Z i ∧ i <Z lengthZ cur) →
    Path start (nthState cur i) p

  LayerComplete : Int → List State → Set
  LayerComplete p cur =
    (t : State) →
    Path start t p →
    Member t cur

  SuccessfulPathsAtLeast : Int → Set
  SuccessfulPathsAtLeast p =
    (t : State) →
    (n : Int) →
    Path start t n →
    success t →
    p ≤Z n

  OuterInvariant : Int → List State → Set
  OuterInvariant p cur =
    zeroZ ≤Z p ∧
    AllAtLayer p cur ∧
    LayerComplete p cur ∧
    SuccessfulPathsAtLeast p

  SuccessorsFromPrefix :
    List State →
    List State →
    Int →
    Set
  SuccessorsFromPrefix cur nxt upper =
    (l : Int) →
    (zeroZ ≤Z l ∧ l <Z lengthZ nxt) →
    Exists Int λ j →
      (zeroZ ≤Z j ∧ j <Z upper) ∧
      Move (nthState cur j) (nthState nxt l)

  PrefixMovesIncluded :
    List State →
    List State →
    Int →
    Set
  PrefixMovesIncluded cur nxt upper =
    (j k : Int) →
    (zeroZ ≤Z j ∧ j <Z upper) →
    (zeroZ ≤Z k ∧
     k <Z lengthZ (moves (nthState cur j))) →
    Member (nthState (moves (nthState cur j)) k) nxt

  PrefixHasNoSuccess :
    List State →
    Int →
    Set
  PrefixHasNoSuccess cur upper =
    (j : Int) →
    (zeroZ ≤Z j ∧ j <Z upper) →
    Not (success (nthState cur j))

  InnerInvariant :
    List State →
    List State →
    Int →
    Set
  InnerInvariant cur nxt upper =
    SuccessorsFromPrefix cur nxt upper ∧
    PrefixMovesIncluded cur nxt upper ∧
    PrefixHasNoSuccess cur upper

  AppendSpecification :
    List State →
    List State →
    List State →
    Set
  AppendSpecification leftList rightList combined =
    lengthZ combined ≡ addInt (lengthZ leftList) (lengthZ rightList) ∧
    ((i : Int) →
      (zeroZ ≤Z i ∧ i <Z lengthZ leftList) →
      nthState combined i ≡ nthState leftList i) ∧
    ((i : Int) →
      (lengthZ leftList ≤Z i ∧ i <Z lengthZ combined) →
      nthState combined i ≡
        nthState rightList (subtractInt i (lengthZ leftList)))

  ProcessIndex :
    Int →
    List State →
    List State →
    Int →
    Set
  ProcessIndex p cur nxt i =
    let s = nthState cur i
    in
    IfProp
      (success s)
      (Path start s p)
      (let newlyFound = moves s
           combined = append newlyFound nxt
       in
       AppendSpecification newlyFound nxt combined →
       InnerInvariant cur combined (addInt i oneZ))

  ForLoopBody :
    Int →
    List State →
    Int →
    List State →
    Set
  ForLoopBody p cur lastIndex nxt =
    (i : Int) →
    ((zeroZ ≤Z i ∧ i ≤Z lastIndex) ∧
     InnerInvariant cur nxt i) →
    ProcessIndex p cur nxt i

  AfterForLoop :
    Int →
    List State →
    Int →
    List State →
    Set
  AfterForLoop p cur lastIndex nxt =
    InnerInvariant cur nxt (addInt lastIndex oneZ) →
    OuterInvariant (addInt p oneZ) nxt

  NonemptyCurrentLayer : Int → List State → Set
  NonemptyCurrentLayer p cur =
    let lastIndex = subtractInt (lengthZ cur) oneZ
    in
    (zeroZ ≤Z addInt lastIndex oneZ →
     InnerInvariant cur [] zeroZ ∧
     ((nxt : List State) →
       ForLoopBody p cur lastIndex nxt ∧
       AfterForLoop p cur lastIndex nxt)) ∧
    (addInt lastIndex oneZ <Z zeroZ →
     OuterInvariant (addInt p oneZ) [])

  NoReachableSuccess : Set
  NoReachableSuccess =
    (t : State) →
    (n : Int) →
    success t →
    Not (Path start t n)

  LoopStep : Int → List State → Set
  LoopStep p cur =
    IfSet
      (intLess zeroZ (lengthZ cur))
      (NonemptyCurrentLayer p cur)
      NoReachableSuccess

  LoopVerificationCondition : Set
  LoopVerificationCondition =
    (p : Int) →
    (cur : List State) →
    OuterInvariant p cur →
    LoopStep p cur

  InitialConsSpecification :
    List State →
    State →
    List State →
    Set
  InitialConsSpecification oldList newHead newList =
    lengthZ newList ≡ addInt oneZ (lengthZ oldList) ∧
    nthState newList zeroZ ≡ newHead ∧
    ((i : Int) →
      (zeroZ <Z i ∧ i ≤Z lengthZ oldList) →
      nthState newList i ≡
        nthState oldList (subtractInt i oneZ))

  bfs-vc : Set
  bfs-vc =
    let oldList = [] {A = State}
        newHead = start
        newList = newHead ∷ oldList
    in
    InitialConsSpecification oldList newHead newList →
    OuterInvariant zeroZ newList ∧
    LoopVerificationCondition
