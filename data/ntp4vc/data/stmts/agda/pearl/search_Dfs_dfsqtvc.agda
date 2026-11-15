-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/search_Dfs_dfsqtvc: the depth-first-search verification condition for
-- bounded recursive search, successful return, loop-invariant preservation,
-- and exhaustion without a reachable successful state. This file contains no proof.

{-# OPTIONS --safe #-}

module search_Dfs_dfsqtvc where

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

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

module SearchTheory
  (State : Set)
  (defaultState : State)
  (moves : State → List State)
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

  data Outcome : Set where
    no-solution : Outcome
    solution    : State → Int → Outcome

  NoSolutionWithin : State → Int → Set
  NoSolutionWithin source bound =
    (t : State) →
    (n : Int) →
    (zeroZ ≤Z n ∧ n ≤Z bound) →
    success t →
    Not (Path source t n)

  NoSuccessfulPathBelow :
    List State →
    Int →
    Int →
    Set
  NoSuccessfulPathBelow mv upper bound =
    (j : Int) →
    (t : State) →
    (n : Int) →
    (zeroZ ≤Z j ∧ j <Z upper) →
    Path (nthState mv j) t n →
    success t →
    Not (zeroZ ≤Z n ∧ n <Z bound)

  ImmediateSuccess : Int → Int → State → Set
  ImmediateSuccess p m s =
    Path s s zeroZ ∧
    success s ∧
    zeroZ ≤Z zeroZ ∧
    zeroZ ≤Z subtractInt m p

  RecursiveOutcomeContract :
    State →
    Int →
    Int →
    Outcome →
    Set
  RecursiveOutcomeContract child m nextDepth no-solution =
    NoSolutionWithin child (subtractInt m nextDepth)
  RecursiveOutcomeContract child m nextDepth (solution t n) =
    Path child t n ∧
    success t ∧
    zeroZ ≤Z n ∧
    n ≤Z subtractInt m nextDepth

  RecursiveOutcomeContinuation :
    Int →
    Int →
    State →
    List State →
    Int →
    Outcome →
    Set
  RecursiveOutcomeContinuation p m source mv i no-solution =
    NoSuccessfulPathBelow
      mv
      (addInt i oneZ)
      (subtractInt m p)
  RecursiveOutcomeContinuation p m source mv i (solution t n) =
    let returnedLength = addInt n oneZ
    in
    Path source t returnedLength ∧
    success t ∧
    zeroZ ≤Z returnedLength ∧
    returnedLength ≤Z subtractInt m p

  RecursiveCallObligation :
    Int →
    Int →
    State →
    List State →
    Int →
    Set
  RecursiveCallObligation p m source mv i =
    let nextDepth = addInt p oneZ
        child = nthState mv i
    in
    ((zeroZ ≤Z subtractInt m p ∧
      subtractInt m nextDepth <Z subtractInt m p) ∧
     zeroZ ≤Z nextDepth ∧
     nextDepth ≤Z addInt m oneZ) ∧
    ((outcome : Outcome) →
      RecursiveOutcomeContract child m nextDepth outcome →
      RecursiveOutcomeContinuation p m source mv i outcome)

  IterationObligation :
    Int →
    Int →
    State →
    List State →
    Int →
    Set
  IterationObligation p m source mv lastIndex =
    (i : Int) →
    ((zeroZ ≤Z i ∧ i ≤Z lastIndex) ∧
     NoSuccessfulPathBelow mv i (subtractInt m p)) →
    RecursiveCallObligation p m source mv i

  NonemptyMovesCase :
    Int →
    Int →
    State →
    List State →
    Int →
    Set
  NonemptyMovesCase p m source mv lastIndex =
    zeroZ ≤Z addInt lastIndex oneZ →
    NoSuccessfulPathBelow mv zeroZ (subtractInt m p) ∧
    IterationObligation p m source mv lastIndex

  LoopExhaustion :
    Int →
    Int →
    State →
    List State →
    Int →
    Set
  LoopExhaustion p m source mv lastIndex =
    NoSuccessfulPathBelow
      mv
      (addInt lastIndex oneZ)
      (subtractInt m p) →
    NoSolutionWithin source (subtractInt m p)

  EmptyMovesCase :
    Int →
    Int →
    State →
    Int →
    Set
  EmptyMovesCase p m source lastIndex =
    addInt lastIndex oneZ <Z zeroZ →
    NoSolutionWithin source (subtractInt m p)

  SearchChildren : Int → Int → State → Set
  SearchChildren p m source =
    let mv = moves source
        lastIndex = subtractInt (lengthZ mv) oneZ
    in
    (NonemptyMovesCase p m source mv lastIndex ∧
     LoopExhaustion p m source mv lastIndex) ∧
    EmptyMovesCase p m source lastIndex

  DfsResult : Int → Int → State → Set
  DfsResult p m source =
    IfSet
      (intLess m p)
      (NoSolutionWithin source (subtractInt m p))
      (IfProp
        (success source)
        (ImmediateSuccess p m source)
        (SearchChildren p m source))

  dfs-vc : Set
  dfs-vc =
    (p : Int) →
    (m : Int) →
    (source : State) →
    zeroZ ≤Z p →
    p ≤Z addInt m oneZ →
    DfsResult p m source
