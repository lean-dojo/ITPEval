-- Statement-only formalization of thousand-theorems corpus artifact Q5171652,
-- "Corners theorem": a sufficiently dense finite subset of an initial square
-- of natural numbers contains a nontrivial corner. This file contains no proof.

{-# OPTIONS --safe #-}

module Q5171652_corners_theorem where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

_!=_ :
  {A : Set} ->
  A ->
  A ->
  Set
x != y =
  Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=     : {n : Nat} -> zero <=N n
  suc<=suc   : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

powNat : Nat -> Nat -> Nat
powNat base zero =
  1
powNat base (suc exponent) =
  base * powNat base exponent

maxNat : Nat -> Nat -> Nat
maxNat zero n =
  n
maxNat m zero =
  m
maxNat (suc m) (suc n) =
  suc (maxNat m n)

factorial : Nat -> Nat
factorial zero =
  1
factorial (suc n) =
  suc n * factorial n

stepBound : Nat -> Nat
stepBound n =
  n * powNat 4 n

iterateStepBound : Nat -> Nat -> Nat
iterateStepBound zero start =
  start
iterateStepBound (suc count) start =
  iterateStepBound count (stepBound start)

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) -> addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) -> addR x zeroR == x
    add-inverseR :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) -> multiplyR x oneR == x
    multiply-zeroR :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexiveR :
      (x : R) -> lessOrEqualR x x
    order-transitiveR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-totalR :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-orderR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-additionR :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNat-multiplicationR :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) ->
              P x ->
              lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) ->
                P x ->
                lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) : Set1 where
  field
    forwardR :
      R -> S
    backwardR :
      S -> R
    forward-after-backwardR :
      (y : S) -> forwardR (backwardR y) == y
    backward-after-forwardR :
      (x : R) -> backwardR (forwardR x) == x
    forward-zeroR :
      forwardR (zeroR source) == zeroR target
    forward-oneR :
      forwardR (oneR source) == oneR target
    forward-addR :
      (x y : R) ->
      forwardR (addR source x y) ==
      addR target (forwardR x) (forwardR y)
    forward-multiplyR :
      (x y : R) ->
      forwardR (multiplyR source x y) ==
      multiplyR target (forwardR x) (forwardR y)
    forward-negateR :
      (x : R) ->
      forwardR (negateR source x) ==
      negateR target (forwardR x)
    forward-reciprocalR :
      (x : R) ->
      forwardR (reciprocalR source x) ==
      reciprocalR target (forwardR x)
    forward-fromNatR :
      (n : Nat) ->
      forwardR (fromNatR source n) == fromNatR target n
    forward-orderR :
      (x y : R) ->
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) : Set2 where
  field
    equivalent-complete-ordered-field :
      (S : Set) ->
      (other : CompleteOrderedField S) ->
      CompleteOrderedFieldEquivalence reals other

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

divideR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divideR reals x y =
  multiplyR reals x (reciprocalR reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

powerR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
powerR reals x zero =
  oneR reals
powerR reals x (suc n) =
  multiplyR reals (powerR reals x n) x

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals term zero =
  zeroR reals
sumFirst reals term (suc n) =
  addR reals
    (sumFirst reals term n)
    (term n)

exponentialTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divideR reals
    (powerR reals x n)
    (fromNatR reals (factorial n))

exponentialPartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialPartialSum reals x n =
  sumFirst reals
    (exponentialTerm reals x)
    (suc n)

Converges :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
Converges reals sequence limit =
  (epsilon : _) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      Both
        (lessOrEqualR reals
          (negateR reals epsilon)
          (subtractR reals (sequence n) limit))
        (lessOrEqualR reals
          (subtractR reals (sequence n) limit)
          epsilon))

Exponential :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
Exponential reals x y =
  Converges reals (exponentialPartialSum reals x) y

Logarithm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
Logarithm reals x y =
  Both
    (StrictLess reals (zeroR reals) x)
    (Exponential reals y x)

NatFloor :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  Set
NatFloor reals x floor =
  Either
    (Both
      (lessOrEqualR reals x (zeroR reals))
      (floor == zero))
    (Both
      (lessOrEqualR reals (zeroR reals) x)
      (Both
        (lessOrEqualR reals (fromNatR reals floor) x)
        (StrictLess reals x (fromNatR reals (suc floor)))))

NatCeiling :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  Set
NatCeiling reals x ceiling =
  Either
    (Both
      (lessOrEqualR reals x (zeroR reals))
      (ceiling == zero))
    (Exists Nat
      (\ predecessor ->
        Both
          (ceiling == suc predecessor)
          (Both
            (StrictLess reals
              (fromNatR reals predecessor)
              x)
            (lessOrEqualR reals
              x
              (fromNatR reals (suc predecessor))))))

Minimum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
Minimum reals x y result =
  Either
    (Both (result == x) (lessOrEqualR reals x y))
    (Both (result == y) (lessOrEqualR reals y x))

InitialRegularityBound :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  Nat ->
  Set
InitialRegularityBound {R} reals epsilon lower result =
  Exists R
    (\ numeratorLog ->
      Both
        (Logarithm reals
          (divideR reals
            (fromNatR reals 100)
            (powerR reals epsilon 5))
          numeratorLog)
        (Exists R
          (\ denominatorLog ->
            Both
              (Logarithm reals
                (fromNatR reals 4)
                denominatorLog)
              (Exists Nat
                (\ logarithmicFloor ->
                  Both
                    (NatFloor reals
                      (divideR reals numeratorLog denominatorLog)
                      logarithmicFloor)
                    (result ==
                      maxNat 7
                        (maxNat lower
                          (suc logarithmicFloor))))))))

RegularityBound :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  Nat ->
  Set
RegularityBound reals epsilon lower result =
  Exists Nat
    (\ iterationCount ->
      Both
        (NatFloor reals
          (divideR reals
            (fromNatR reals 4)
            (powerR reals epsilon 5))
          iterationCount)
        (Exists Nat
          (\ initial ->
            Both
              (InitialRegularityBound reals epsilon lower initial)
              (Exists Nat
                (\ iterated ->
                  Both
                    (iterated ==
                      iterateStepBound iterationCount initial)
                    (result ==
                      iterated * powNat 16 iterated))))))

TriangleRemovalBound :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
TriangleRemovalBound {R} reals epsilon result =
  Exists Nat
    (\ ceilingFourOverEpsilon ->
      Both
        (NatCeiling reals
          (divideR reals (fromNatR reals 4) epsilon)
          ceilingFourOverEpsilon)
        (Exists Nat
          (\ regularityBound ->
            Both
              (RegularityBound reals
                (divideR reals epsilon (fromNatR reals 8))
                ceilingFourOverEpsilon
                regularityBound)
              (Exists R
                (\ firstTerm ->
                  Both
                    (firstTerm ==
                      reciprocalR reals
                        (fromNatR reals
                          (2 * powNat ceilingFourOverEpsilon 3)))
                    (Exists R
                      (\ epsilonMinimum ->
                        Both
                          (Minimum reals
                            (oneR reals)
                            epsilon
                            epsilonMinimum)
                          (Exists R
                            (\ secondTerm ->
                              Both
                                (secondTerm ==
                                  multiplyR reals
                                    (subtractR reals
                                      (oneR reals)
                                      (divideR reals
                                        epsilonMinimum
                                        (fromNatR reals 4)))
                                    (powerR reals
                                      (divideR reals
                                        epsilon
                                        (fromNatR reals
                                          (16 * regularityBound)))
                                      3))
                                (Minimum reals
                                  firstTerm
                                  secondTerm
                                  result))))))))))

CornersTheoremBound :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  Set
CornersTheoremBound {R} reals epsilon result =
  Exists R
    (\ triangleBound ->
      Both
        (TriangleRemovalBound reals
          (divideR reals epsilon (fromNatR reals 9))
          triangleBound)
        (Exists Nat
          (\ inverseFloor ->
            Both
              (NatFloor reals
                (reciprocalR reals
                  (multiplyR reals
                    triangleBound
                    (fromNatR reals 27)))
                inverseFloor)
              (result == suc inverseFloor))))

record Pair : Set where
  constructor pair
  field
    firstNat  : Nat
    secondNat : Nat

open Pair

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc n) =
  false
natEqual (suc m) zero =
  false
natEqual (suc m) (suc n) =
  natEqual m n

andBool : Bool -> Bool -> Bool
andBool true value =
  value
andBool false value =
  false

pairEqual : Pair -> Pair -> Bool
pairEqual p q =
  andBool
    (natEqual (firstNat p) (firstNat q))
    (natEqual (secondNat p) (secondNat q))

contains : Pair -> List Pair -> Bool
contains point [] =
  false
contains point (head ∷ tail) with pairEqual point head
... | true =
  true
... | false =
  contains point tail

data IsTrue : Bool -> Set where
  true-witness : IsTrue true

data NoDuplicates : List Pair -> Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {head : Pair} ->
    {tail : List Pair} ->
    contains head tail == false ->
    NoDuplicates tail ->
    NoDuplicates (head ∷ tail)

record FiniteSet : Set where
  constructor finite-set
  field
    elements      : List Pair
    no-duplicates : NoDuplicates elements

open FiniteSet

length : List Pair -> Nat
length [] =
  zero
length (head ∷ tail) =
  suc (length tail)

Member : Pair -> FiniteSet -> Set
Member point finite =
  IsTrue (contains point (elements finite))

ContainedInInitialSquare : FiniteSet -> Nat -> Set
ContainedInInitialSquare finite n =
  (point : Pair) ->
  Member point finite ->
  Both
    (firstNat point <N n)
    (secondNat point <N n)

record IsCorner
  (finite : FiniteSet)
  (x1 y1 x2 y2 : Nat) :
  Set where

  field
    first-first-member :
      Member (pair x1 y1) finite
    first-second-member :
      Member (pair x1 y2) finite
    second-first-member :
      Member (pair x2 y1) finite
    additive-relation :
      x1 + y2 == x2 + y1

IsCornerFree : FiniteSet -> Set
IsCornerFree finite =
  (x1 y1 x2 y2 : Nat) ->
  IsCorner finite x1 y1 x2 y2 ->
  x1 == x2

corners-theorem-nat : Set2
corners-theorem-nat =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  (n : Nat) ->
  Exists Nat
    (\ bound ->
      Both
        (CornersTheoremBound reals
          (divideR reals epsilon (fromNatR reals 9))
          bound)
        (bound <=N n)) ->
  (finite : FiniteSet) ->
  ContainedInInitialSquare finite n ->
  lessOrEqualR reals
    (multiplyR reals
      epsilon
      (fromNatR reals (n * n)))
    (fromNatR reals (length (elements finite))) ->
  Not (IsCornerFree finite)
