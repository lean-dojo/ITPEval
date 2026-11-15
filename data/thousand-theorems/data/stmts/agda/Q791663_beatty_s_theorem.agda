-- Statement-only formalization of thousand-theorems corpus artifact Q791663,
-- "Beatty's theorem": conjugate Beatty sequences complement one another, and
-- for an irrational parameter their positive parts partition the positive
-- integers. This file contains no proof.

{-# OPTIONS --safe #-}

module Q791663_beatty_s_theorem where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

  constructor witness
  field
    value    : A
    property : P value

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessThanR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) ->
      addR x y == addR y x
    add-associative :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zero :
      (x : R) ->
      addR x zeroR == x
    add-inverse :
      (x : R) ->
      addR x (negateR x) == zeroR
    negate-involutive :
      (x : R) ->
      negateR (negateR x) == x

    multiply-commutative :
      (x y : R) ->
      multiplyR x y == multiplyR y x
    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) ->
      multiplyR x oneR == x
    multiply-zero :
      (x : R) ->
      multiplyR x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverse-zero :
      inverseR zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-irreflexive :
      (x : R) ->
      lessThanR x x ->
      Bottom
    order-transitive :
      (x y z : R) ->
      lessThanR x y ->
      lessThanR y z ->
      lessThanR x z
    order-trichotomy :
      (x y : R) ->
      lessThanR x y or
      (x == y or lessThanR y x)
    add-order :
      (x y z : R) ->
      lessThanR x y ->
      lessThanR (addR z x) (addR z y)
    multiply-positive :
      (x y : R) ->
      lessThanR zeroR x ->
      lessThanR zeroR y ->
      lessThanR zeroR (multiplyR x y)
    zero-less-than-one :
      lessThanR zeroR oneR

    fromNat-zero :
      fromNatR zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNatR (m + n) ==
      addR (fromNatR m) (fromNatR n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) ==
      multiplyR (fromNatR m) (fromNatR n)
    fromNat-injective :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessThanR x (fromNatR n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessThanR x upper or x == upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessThanR x supremum or x == supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessThanR x upper or x == upper) ->
            lessThanR supremum upper or supremum == upper))

open CompleteOrderedField

LessOrEqual :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
LessOrEqual reals x y =
  lessThanR reals x y or x == y

divideR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divideR reals x y =
  multiplyR reals x (inverseR reals y)

fromIntR :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  R
fromIntR reals (pos n) =
  fromNatR reals n
fromIntR reals (negsuc n) =
  negateR reals (fromNatR reals (suc n))

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) :
  Set1 where

  field
    forwardR :
      R -> S
    backwardR :
      S -> R
    forward-after-backwardR :
      (y : S) ->
      forwardR (backwardR y) == y
    backward-after-forwardR :
      (x : R) ->
      backwardR (forwardR x) == x
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
    forward-inverseR :
      (x : R) ->
      forwardR (inverseR source x) ==
      inverseR target (forwardR x)
    forward-fromNatR :
      (n : Nat) ->
      forwardR (fromNatR source n) ==
      fromNatR target n
    forward-orderR :
      (x y : R) ->
      Iff
        (lessThanR source x y)
        (lessThanR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set2 where

  field
    equivalent-complete-ordered-field :
      (S : Set) ->
      (other : CompleteOrderedField S) ->
      CompleteOrderedFieldEquivalence reals other

successorInt : Int -> Int
successorInt (pos n) =
  pos (suc n)
successorInt (negsuc zero) =
  pos zero
successorInt (negsuc (suc n)) =
  negsuc n

predecessorInt : Int -> Int
predecessorInt (pos zero) =
  negsuc zero
predecessorInt (pos (suc n)) =
  pos n
predecessorInt (negsuc n) =
  negsuc (suc n)

negateInt : Int -> Int
negateInt (pos zero) =
  pos zero
negateInt (pos (suc n)) =
  negsuc n
negateInt (negsuc n) =
  pos (suc n)

record IntegerFloor
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    floorR :
      R -> Int
    floor-lower :
      (x : R) ->
      LessOrEqual reals
        (fromIntR reals (floorR x))
        x
    floor-upper :
      (x : R) ->
      lessThanR reals x
        (fromIntR reals (successorInt (floorR x)))

open IntegerFloor

ceilingR :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  IntegerFloor reals ->
  R ->
  Int
ceilingR {reals = reals} floors x =
  negateInt (floorR floors (negateR reals x))

Region : Set -> Set1
Region A =
  A -> Set

Complement :
  {A : Set} ->
  Region A ->
  Region A
Complement P x =
  Not (P x)

Intersection :
  {A : Set} ->
  Region A ->
  Region A ->
  Region A
Intersection P Q x =
  P x and Q x

Union :
  {A : Set} ->
  Region A ->
  Region A ->
  Region A
Union P Q x =
  P x or Q x

SymmetricDifference :
  {A : Set} ->
  Region A ->
  Region A ->
  Region A
SymmetricDifference P Q =
  Union
    (Intersection P (Complement Q))
    (Intersection Q (Complement P))

RegionEquality :
  {A : Set} ->
  Region A ->
  Region A ->
  Set
RegionEquality {A = A} P Q =
  (x : A) ->
  Iff (P x) (Q x)

HolderConjugate :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
HolderConjugate reals r s =
  lessThanR reals (oneR reals) r
  and
  (lessThanR reals (oneR reals) s
  and
  addR reals
    (inverseR reals r)
    (inverseR reals s)
  == oneR reals)

Irrational :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Irrational reals x =
  (numerator denominator : Int) ->
  denominator != pos zero ->
  x !=
    divideR reals
      (fromIntR reals numerator)
      (fromIntR reals denominator)

IntPositive :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  Set
IntPositive reals k =
  lessThanR reals
    (zeroR reals)
    (fromIntR reals k)

BeattySet :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  IntegerFloor reals ->
  R ->
  Region Int
BeattySet reals floors r j =
  Exists Int
    (\ k ->
      floorR floors
        (multiplyR reals (fromIntR reals k) r)
      == j)

BeattyPrimeSet :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  IntegerFloor reals ->
  R ->
  Region Int
BeattyPrimeSet reals floors r j =
  Exists Int
    (\ k ->
      predecessorInt
        (ceilingR floors
          (multiplyR reals (fromIntR reals k) r))
      == j)

PositiveBeattySet :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  IntegerFloor reals ->
  R ->
  Region Int
PositiveBeattySet reals floors r j =
  Exists Int
    (\ k ->
      IntPositive reals k
      and
      floorR floors
        (multiplyR reals (fromIntR reals k) r)
      == j)

compl-beatty-seq : Set2
compl-beatty-seq =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (floors : IntegerFloor reals) ->
  (r s : R) ->
  HolderConjugate reals r s ->
  RegionEquality
    (Complement (BeattySet reals floors r))
    (BeattyPrimeSet reals floors s)

beatty-s-theorem : Set2
beatty-s-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (floors : IntegerFloor reals) ->
  (r s : R) ->
  HolderConjugate reals r s ->
  Irrational reals r ->
  RegionEquality
    (SymmetricDifference
      (PositiveBeattySet reals floors r)
      (PositiveBeattySet reals floors s))
    (IntPositive reals)
