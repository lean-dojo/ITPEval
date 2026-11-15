-- Statement-only formalization of PutnamBench corpus artifact putnam_2006_b3
-- (putnambench__agda__putnam_2006_b3): the maximum number of unordered
-- linear bipartitions of an n-point subset of the real plane is n choose 2
-- plus one. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2006B3 where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
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
  {a : Level} {A : Set a} ->
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
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

Positive : Nat -> Set
Positive n =
  oneN <=N n

choose : Nat -> Nat -> Nat
choose n zero =
  oneN
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n (suc k) + choose n k

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

record Point (R : Set) : Set where
  constructor point
  field
    xCoordinate : R
    yCoordinate : R

open Point

PointEqual :
  {R : Set} ->
  Point R ->
  Point R ->
  Set
PointEqual p q =
  xCoordinate p == xCoordinate q
  and
  yCoordinate p == yCoordinate q

PointSet : Set -> Set1
PointSet R =
  Point R -> Set

SamePointSet :
  {R : Set} ->
  PointSet R ->
  PointSet R ->
  Set
SamePointSet {R} leftSet rightSet =
  (p : Point R) ->
  Iff (leftSet p) (rightSet p)

record SetFamily (R : Set) : Set1 where
  field
    contains :
      PointSet R ->
      Set
    contains-respects :
      (leftSet rightSet : PointSet R) ->
      SamePointSet leftSet rightSet ->
      Iff (contains leftSet) (contains rightSet)

open SetFamily

SameFamily :
  {R : Set} ->
  SetFamily R ->
  SetFamily R ->
  Set1
SameFamily {R} leftFamily rightFamily =
  (pointSet : PointSet R) ->
  Iff
    (contains leftFamily pointSet)
    (contains rightFamily pointSet)

record HasCardinality
  {a p e : Level}
  {A : Set a}
  (equivalent : A -> A -> Set e)
  (belongs : A -> Set p)
  (cardinality : Nat) :
  Set (a ⊔ p ⊔ e) where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-belongs :
      (index : Fin cardinality) ->
      belongs (enumerate index)
    enumeration-complete :
      (item : A) ->
      belongs item ->
      Exists (Fin cardinality)
        (\ index ->
          equivalent item (enumerate index))
    enumeration-injective :
      (leftIndex rightIndex : Fin cardinality) ->
      equivalent
        (enumerate leftIndex)
        (enumerate rightIndex) ->
      leftIndex == rightIndex

PointSetCardinality :
  {R : Set} ->
  PointSet R ->
  Nat ->
  Set
PointSetCardinality pointSet cardinality =
  HasCardinality PointEqual pointSet cardinality

FamilyCardinality :
  {R : Set} ->
  SetFamily R ->
  Nat ->
  Set1
FamilyCardinality family cardinality =
  HasCardinality SamePointSet (contains family) cardinality

UnionIs :
  {R : Set} ->
  PointSet R ->
  PointSet R ->
  PointSet R ->
  Set
UnionIs {R} whole leftSet rightSet =
  (p : Point R) ->
  Iff
    (whole p)
    (leftSet p or rightSet p)

Disjoint :
  {R : Set} ->
  PointSet R ->
  PointSet R ->
  Set
Disjoint {R} leftSet rightSet =
  (p : Point R) ->
  Not (leftSet p and rightSet p)

LineSeparates :
  {R : Set} ->
  CompleteOrderedRealField R ->
  PointSet R ->
  PointSet R ->
  Set
LineSeparates {R} reals upperSet lowerSet =
  Exists R
    (\ slope ->
      Exists R
        (\ intercept ->
          ((p : Point R) ->
            upperSet p ->
            StrictLess reals
              (add reals
                (multiply reals slope (xCoordinate p))
                intercept)
              (yCoordinate p))
          and
          ((p : Point R) ->
            lowerSet p ->
            StrictLess reals
              (yCoordinate p)
              (add reals
                (multiply reals slope (xCoordinate p))
                intercept))))

IsLinearPartition :
  {R : Set} ->
  CompleteOrderedRealField R ->
  PointSet R ->
  SetFamily R ->
  Set1
IsLinearPartition {R} reals whole family =
  FamilyCardinality family twoN
  and
  Exists (PointSet R)
    (\ upperSet ->
      contains family upperSet
      and
      Exists (PointSet R)
        (\ lowerSet ->
          contains family lowerSet
          and
          Not (SamePointSet upperSet lowerSet)
          and
          UnionIs whole upperSet lowerSet
          and
          Disjoint upperSet lowerSet
          and
          LineSeparates reals upperSet lowerSet))

LinearPartitionCount :
  {R : Set} ->
  CompleteOrderedRealField R ->
  PointSet R ->
  Nat ->
  Set1
LinearPartitionCount {R} reals pointSet count =
  HasCardinality
    SameFamily
    (IsLinearPartition reals pointSet)
    count

putnam-2006-b3-solution : Nat -> Nat
putnam-2006-b3-solution n =
  choose n twoN + oneN

IsMaximumLinearPartitionCount :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Nat ->
  Set1
IsMaximumLinearPartitionCount {R} reals n maximum =
  Exists (PointSet R)
    (\ pointSet ->
      PointSetCardinality pointSet n
      and
      LinearPartitionCount reals pointSet maximum)
  and
  ((pointSet : PointSet R) ->
    (count : Nat) ->
    PointSetCardinality pointSet n ->
    LinearPartitionCount reals pointSet count ->
    count <=N maximum)

putnam-2006-b3 : Set1
putnam-2006-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  Positive n ->
  IsMaximumLinearPartitionCount
    reals
    n
    (putnam-2006-b3-solution n)
