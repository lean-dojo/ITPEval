-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/queens_NQueensSets_t3qtvc: the finite-integer-set verification
-- condition for the recursive N-queens solution enumerator, including its
-- loop invariants and base case. This file contains no proof.

{-# OPTIONS --safe #-}

module queens_NQueensSets_t3qtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _<N_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

Not : Set → Set
Not proposition = proposition → ⊥

record _∧_ (left right : Set) : Set where
  constructor both
  field
    first  : left
    second : right

record _↔_ (left right : Set) : Set where
  constructor iff
  field
    forward  : left → right
    backward : right → left

record Exists (A : Set) (property : A → Set) : Set where
  constructor witness
  field
    value : A
    proof : property value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

_<N_ : Nat → Nat → Set
m <N n = natLess m n ≡ true

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

infixl 6 _+Z_ _-Z_

_+Z_ : Int → Int → Int
_+Z_ = addInt

_-Z_ : Int → Int → Int
_-Z_ = subtractInt

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

contains : Int → List Int → Bool
contains x [] = false
contains x (y ∷ ys) with intEqual x y
... | true = true
... | false = contains x ys

removeAll : Int → List Int → List Int
removeAll x [] = []
removeAll x (y ∷ ys) with intEqual x y
... | true = removeAll x ys
... | false = y ∷ removeAll x ys

nub : List Int → List Int
nub [] = []
nub (x ∷ xs) with contains x xs
... | true = nub xs
... | false = x ∷ nub xs

differenceList : List Int → List Int → List Int
differenceList [] ys = []
differenceList (x ∷ xs) ys with contains x ys
... | true = differenceList xs ys
... | false = x ∷ differenceList xs ys

record FSet : Set where
  constructor fset
  field
    elements : List Int

open FSet

empty : FSet
empty = fset []

memberBool : Int → FSet → Bool
memberBool x set = contains x (elements set)

member : Int → FSet → Set
member x set = memberBool x set ≡ true

subset : FSet → FSet → Set
subset leftSet rightSet =
  (x : Int) → member x leftSet → member x rightSet

setEqual : FSet → FSet → Set
setEqual leftSet rightSet =
  subset leftSet rightSet ∧ subset rightSet leftSet

nonemptyBool : FSet → Bool
nonemptyBool (fset []) = false
nonemptyBool (fset (_ ∷ _)) = true

Nonempty : FSet → Set
Nonempty set = nonemptyBool set ≡ true

difference : FSet → FSet → FSet
difference leftSet rightSet =
  fset (differenceList (elements leftSet) (elements rightSet))

insert : Int → FSet → FSet
insert x set with memberBool x set
... | true = set
... | false = fset (x ∷ elements set)

erase : Int → FSet → FSet
erase x set = fset (removeAll x (elements set))

card : FSet → Nat
card set = length (nub (elements set))

cardZ : FSet → Int
cardZ set = pos (card set)

minimumPair : Int → Int → Int
minimumPair x y with intLessOrEqual x y
... | true = x
... | false = y

minimumFrom : Int → List Int → Int
minimumFrom current [] = current
minimumFrom current (x ∷ xs) =
  minimumFrom (minimumPair current x) xs

minimum : FSet → Int
minimum set with elements set
... | [] = zeroZ
... | x ∷ xs = minimumFrom x xs

updateInt :
  {A : Set} →
  (Int → A) →
  Int →
  A →
  Int →
  A
updateInt function key new-value argument with intEqual argument key
... | true = new-value
... | false = function argument

EqPrefixInt :
  (Int → Int) →
  (Int → Int) →
  Int →
  Set
EqPrefixInt left right bound =
  (index : Int) →
  zeroZ ≤Z index ∧ index <Z bound →
  left index ≡ right index

EqPrefixSolutions :
  (Int → Int → Int) →
  (Int → Int → Int) →
  Int →
  Set
EqPrefixSolutions left right bound =
  (index : Int) →
  zeroZ ≤Z index ∧ index <Z bound →
  (column : Int) →
  left index column ≡ right index column

PartialSolution :
  Int →
  Int →
  (Int → Int) →
  Set
PartialSolution n k solution =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z k →
  ((zeroZ ≤Z solution i ∧ solution i <Z n)
   ∧
   ((j : Int) →
    zeroZ ≤Z j ∧ j <Z i →
    (Not (solution i ≡ solution j)
     ∧
     Not ((solution i -Z solution j) ≡ (i -Z j))
     ∧
     Not ((solution i -Z solution j) ≡ (j -Z i)))))

CompleteSolution :
  Int →
  (Int → Int) →
  Set
CompleteSolution n solution =
  PartialSolution n n solution

EqSolution :
  Int →
  (Int → Int) →
  (Int → Int) →
  Set
EqSolution n left right =
  EqPrefixInt left right n

LessSolution :
  Int →
  (Int → Int) →
  (Int → Int) →
  Set
LessSolution n left right =
  Exists Int
    (λ index →
      (zeroZ ≤Z index ∧ index <Z n)
      ∧ EqPrefixInt left right index
      ∧ left index <Z right index)

Sorted :
  Int →
  (Int → Int → Int) →
  Int →
  Int →
  Set
Sorted n solutions lower upper =
  (i j : Int) →
  lower ≤Z i ∧ i <Z j ∧ j <Z upper →
  LessSolution n (solutions i) (solutions j)

AvailableColumns :
  Int →
  Int →
  FSet →
  (Int → Int) →
  Set
AvailableColumns n k available columns =
  (i : Int) →
  member i available ↔
    ((zeroZ ≤Z i ∧ i <Z n)
     ∧
     ((j : Int) →
      zeroZ ≤Z j ∧ j <Z k →
      Not (columns j ≡ i)))

UnusedAscendingDiagonals :
  Int →
  FSet →
  (Int → Int) →
  Set
UnusedAscendingDiagonals k diagonals columns =
  (i : Int) →
  zeroZ ≤Z i →
  Not (member i diagonals) ↔
    ((j : Int) →
     zeroZ ≤Z j ∧ j <Z k →
     Not (columns j ≡ ((i +Z j) -Z k)))

UnusedDescendingDiagonals :
  Int →
  FSet →
  (Int → Int) →
  Set
UnusedDescendingDiagonals k diagonals columns =
  (i : Int) →
  zeroZ ≤Z i →
  Not (member i diagonals) ↔
    ((j : Int) →
     zeroZ ≤Z j ∧ j <Z k →
     Not (columns j ≡ ((i +Z k) -Z j)))

CallPreconditions :
  Int →
  Int →
  FSet →
  Int →
  (Int → Int) →
  FSet →
  FSet →
  Set
CallPreconditions n k available nextSlot columns ascending descending =
  zeroZ ≤Z k
  ∧ (k +Z cardZ available) ≡ n
  ∧ zeroZ ≤Z nextSlot
  ∧ AvailableColumns n k available columns
  ∧ UnusedAscendingDiagonals k ascending columns
  ∧ UnusedDescendingDiagonals k descending columns
  ∧ PartialSolution n k columns

InsertCondition : Int → FSet → FSet → Set
InsertCondition value base result =
  setEqual result (insert value base)
  ∧
  IfSet
    (memberBool value base)
    (card result ≡ card base)
    (cardZ result ≡ (cardZ base +Z oneZ))

RemoveCondition : Int → FSet → FSet → Set
RemoveCondition value base result =
  setEqual result (erase value base)
  ∧
  IfSet
    (memberBool value base)
    (cardZ result ≡ (cardZ base -Z oneZ))
    (card result ≡ card base)

SuccessorSetCondition : FSet → FSet → Set
SuccessorSetCondition source result =
  (i : Int) →
  member i result ↔
    (zeroZ ≤Z i ∧ member (i +Z oneZ) source)

PredecessorSetCondition : FSet → FSet → Set
PredecessorSetCondition source result =
  (i : Int) →
  member i result ↔
    (oneZ ≤Z i ∧ member (i -Z oneZ) source)

CardinalityDecrease : FSet → FSet → Set
CardinalityDecrease before after =
  zeroZ ≤Z cardZ before ∧ card after <N card before

OrderedRemainder : FSet → FSet → Set
OrderedRemainder original remaining =
  (i j : Int) →
  member i (difference original remaining) →
  member j remaining →
  i <Z j

GeneratedSolutions :
  Int →
  Int →
  FSet →
  FSet →
  Int →
  Int →
  (Int → Int) →
  (Int → Int → Int) →
  Set
GeneratedSolutions n k original remaining start finish columns solutions =
  (i : Int) →
  start ≤Z i ∧ i <Z finish →
  CompleteSolution n (solutions i)
  ∧ EqPrefixInt columns (solutions i) k
  ∧ member (solutions i k) (difference original remaining)

EnumeratesProcessedSolutions :
  Int →
  Int →
  FSet →
  FSet →
  Int →
  Int →
  (Int → Int) →
  (Int → Int → Int) →
  Set
EnumeratesProcessedSolutions
  n k original remaining start finish columns solutions =
  (candidate : Int → Int) →
  CompleteSolution n candidate
  ∧ EqPrefixInt columns candidate k
  ∧ member (candidate k) (difference original remaining) →
  member (candidate k) original
  ∧ Not (member (candidate k) remaining)
  ∧ Exists Int
      (λ i →
        (start ≤Z i ∧ i <Z finish)
        ∧ EqSolution n candidate (solutions i))

LoopStateCore :
  Int →
  Int →
  FSet →
  FSet →
  FSet →
  FSet →
  FSet →
  Int →
  Int →
  (Int → Int) →
  (Int → Int) →
  (Int → Int → Int) →
  (Int → Int → Int) →
  Set
LoopStateCore
  n k available ascending descending original remaining
  start finish initialColumns columns initialSolutions solutions =
  subset remaining (difference (difference available ascending) descending)
  ∧ PartialSolution n k columns
  ∧ Sorted n solutions start finish
  ∧ OrderedRemainder original remaining
  ∧ GeneratedSolutions
      n k original remaining start finish columns solutions
  ∧ EnumeratesProcessedSolutions
      n k original remaining start finish columns solutions
  ∧ EqPrefixInt initialColumns columns k
  ∧ EqPrefixSolutions initialSolutions solutions start

LoopStateAt :
  Int →
  Int →
  FSet →
  FSet →
  FSet →
  FSet →
  FSet →
  Int →
  Int →
  (Int → Int) →
  (Int → Int) →
  (Int → Int → Int) →
  (Int → Int → Int) →
  Set
LoopStateAt
  n k available ascending descending original remaining
  start finish initialColumns columns initialSolutions solutions =
  zeroZ ≤Z (finish -Z start)
  ∧ LoopStateCore
      n k available ascending descending original remaining
      start finish initialColumns columns initialSolutions solutions

BatchPostcondition :
  Int →
  Int →
  Int →
  Int →
  (Int → Int) →
  (Int → Int) →
  (Int → Int → Int) →
  (Int → Int → Int) →
  Set
BatchPostcondition
  n k start finish initialColumns columns initialSolutions solutions =
  zeroZ ≤Z (finish -Z start)
  ∧ Sorted n solutions start finish
  ∧
    ((candidate : Int → Int) →
     (CompleteSolution n candidate ∧ EqPrefixInt columns candidate k)
     ↔
     Exists Int
       (λ i →
         (start ≤Z i ∧ i <Z finish)
         ∧ EqSolution n candidate (solutions i)))
  ∧ EqPrefixInt initialColumns columns k
  ∧ EqPrefixSolutions initialSolutions solutions start

RecursiveIteration :
  Int →
  Int →
  FSet →
  FSet →
  FSet →
  FSet →
  Int →
  Int →
  (Int → Int) →
  (Int → Int) →
  (Int → Int → Int) →
  (Int → Int → Int) →
  FSet →
  Int →
  Set
RecursiveIteration
  n k available ascending descending original
  start finish initialColumns columns initialSolutions solutions
  remaining chosen =
  (newDescending : FSet) →
  InsertCondition chosen descending newDescending →
  (shiftedDescending : FSet) →
  SuccessorSetCondition newDescending shiftedDescending →
  (newAscending : FSet) →
  InsertCondition chosen ascending newAscending →
  (shiftedAscending : FSet) →
  PredecessorSetCondition newAscending shiftedAscending →
  (newAvailable : FSet) →
  RemoveCondition chosen available newAvailable →
  (CardinalityDecrease available newAvailable
   ∧
   CallPreconditions
     n (k +Z oneZ) newAvailable finish
     (updateInt columns k chosen)
     shiftedAscending shiftedDescending)
  ∧
  ((newFinish : Int) →
   (newSolutions : Int → Int → Int) →
   (newColumns : Int → Int) →
   BatchPostcondition
     n (k +Z oneZ) finish newFinish
     (updateInt columns k chosen) newColumns
     solutions newSolutions →
   (newRemaining : FSet) →
   RemoveCondition chosen remaining newRemaining →
   CardinalityDecrease remaining newRemaining
   ∧ (((finish -Z start) +Z (newFinish -Z finish))
      ≡ (newFinish -Z start))
   ∧ zeroZ ≤Z (newFinish -Z start)
    ∧ ((k +Z oneZ) -Z oneZ) ≡ k
    ∧ LoopStateCore
        n ((k +Z oneZ) -Z oneZ)
        available ascending descending original newRemaining
        start newFinish initialColumns newColumns
        initialSolutions newSolutions)

LoopStep :
  Int →
  Int →
  FSet →
  FSet →
  FSet →
  FSet →
  Int →
  Int →
  (Int → Int) →
  (Int → Int) →
  (Int → Int → Int) →
  (Int → Int → Int) →
  FSet →
  Set
LoopStep
  n k available ascending descending original
  start finish initialColumns columns initialSolutions solutions remaining =
  IfSet
    (nonemptyBool remaining)
    (Nonempty remaining
     ∧
     RecursiveIteration
       n k available ascending descending original
       start finish initialColumns columns initialSolutions solutions
       remaining (minimum remaining))
    (BatchPostcondition
       n k start finish
       initialColumns columns initialSolutions solutions)

t3-vc : Set
t3-vc =
  (n k : Int) →
  (available : FSet) →
  (start : Int) →
  (columns : Int → Int) →
  (ascending descending : FSet) →
  (solutions : Int → Int → Int) →
  zeroZ ≤Z k →
  (k +Z cardZ available) ≡ n →
  zeroZ ≤Z start →
  AvailableColumns n k available columns →
  UnusedAscendingDiagonals k ascending columns →
  UnusedDescendingDiagonals k descending columns →
  PartialSolution n k columns →
  IfSet
    (nonemptyBool available)
    ((firstDifference : FSet) →
     setEqual firstDifference (difference available ascending) →
     (original : FSet) →
     setEqual original (difference firstDifference descending) →
     ((zeroZ ≡ (start -Z start))
      ∧ LoopStateAt
          n k available ascending descending original original
          start start columns columns solutions solutions)
     ∧
     ((remaining : FSet) →
      (finish : Int) →
      (currentSolutions : Int → Int → Int) →
      (currentColumns : Int → Int) →
      LoopStateAt
        n k available ascending descending original remaining
        start finish columns currentColumns solutions currentSolutions →
      LoopStep
        n k available ascending descending original
        start finish columns currentColumns solutions currentSolutions
        remaining))
    ((oneZ ≡ ((start +Z oneZ) -Z start))
     ∧
     BatchPostcondition
       n k start (start +Z oneZ)
       columns columns
       solutions (updateInt solutions start columns))
