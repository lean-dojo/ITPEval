-- Statement-only formalization of PutnamBench corpus artifact putnam_1978_a6:
-- a nonempty finite set of n points in the real plane determines fewer than
-- 2 * n^(3/2) unordered pairs at Euclidean distance one. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  {level : Level} ->
  Set level ->
  Set level
Not proposition =
  proposition -> Bottom

_!=_ :
  {level : Level} ->
  {A : Set level} ->
  A ->
  A ->
  Set level
x != y =
  Not (x == y)

record _and_
  {left-level right-level : Level}
  (A : Set left-level)
  (B : Set right-level) :
  Set (left-level ⊔ right-level) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {left-level right-level : Level}
  (A : Set left-level)
  (B : Set right-level) :
  Set (left-level ⊔ right-level) where

  left  : A -> A or B
  right : B -> A or B

record Exists
  {element-level property-level : Level}
  (A : Set element-level)
  (P : A -> Set property-level) :
  Set (element-level ⊔ property-level) where

  constructor witness
  field
    value    : A
    property : P value

data _<N_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero <N suc n
  suc<suc  : {m n : Nat} -> m <N n -> suc m <N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {element-level property-level : Level}
  {A : Set element-level}
  (member : A -> Set property-level)
  (cardinality : Nat) :
  Set (element-level ⊔ property-level) where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record HasExtensionalCardinality
  {element-level equivalence-level property-level : Level}
  {A : Set element-level}
  (equivalent : A -> A -> Set equivalence-level)
  (member : A -> Set property-level)
  (cardinality : Nat) :
  Set (element-level ⊔ equivalence-level ⊔ property-level) where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
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
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
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
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual zeroR x ->
      multiply (squareRoot x) (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      squareRoot x == zeroR
    square-root-unique :
      (x y : R) ->
      lessOrEqual zeroR y ->
      multiply y y == x ->
      y == squareRoot x

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals (naturalPower reals x n) x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals (subtract reals center radius) x
  and
  StrictLess reals x (add reals center radius)

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo reals sequence limit =
  (epsilon : _) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms limit =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    limit

exponentialTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divide reals
    (naturalPower reals x n)
    (fromNat reals (factorial n))

ExponentialValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
ExponentialValue reals x value =
  SeriesHasSum reals
    (exponentialTerm reals x)
    value

record StandardRealPowers
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential logarithm : R -> R

    exponential-series :
      (x : R) ->
      ExponentialValue reals x (exponential x)

    exponential-positive :
      (x : R) ->
      StrictLess reals (zeroR reals) (exponential x)

    exponential-injective :
      (x y : R) ->
      exponential x == exponential y ->
      x == y

    exponential-logarithm :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      exponential (logarithm x) == x

open StandardRealPowers

realPower :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  StandardRealPowers reals ->
  R ->
  R ->
  R
realPower {reals = reals} powers base exponent =
  exponential powers
    (multiply reals exponent (logarithm powers base))

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

squaredDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
squaredDistance reals p q =
  add reals
    (square reals
      (subtract reals (x-coordinate p) (x-coordinate q)))
    (square reals
      (subtract reals (y-coordinate p) (y-coordinate q)))

distance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
distance reals p q =
  squareRoot reals (squaredDistance reals p q)

Subset :
  Set ->
  Set1
Subset A =
  A -> Set

SetEqual :
  {A : Set} ->
  Subset A ->
  Subset A ->
  Set
SetEqual left-set right-set =
  (x : _) ->
  (left-set x -> right-set x)
  and
  (right-set x -> left-set x)

TwoPointSet :
  {R : Set} ->
  Point R ->
  Point R ->
  Subset (Point R)
TwoPointSet p q x =
  (x == p) or (x == q)

UnitPair :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Subset (Point R) ->
  Subset (Point R) ->
  Set
UnitPair {R} reals S pair =
  Exists (Point R)
    (\ p ->
      S p
      and
      Exists (Point R)
        (\ q ->
          S q
          and
          SetEqual pair (TwoPointSet p q)
          and
          distance reals p q == oneR reals))

module Putnam1978A6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (powers : StandardRealPowers reals) where

  two : R
  two =
    fromNat reals (suc (suc zero))

  three : R
  three =
    fromNat reals (suc (suc (suc zero)))

  three-halves : R
  three-halves =
    divide reals three two

  bound : Nat -> R
  bound n =
    multiply reals two
      (realPower powers (fromNat reals n) three-halves)

  proposition : Set1
  proposition =
    (S : Subset (Point R)) ->
    (n : Nat) ->
    HasCardinality S n ->
    zero <N n ->
    Exists Nat
      (\ pair-count ->
        HasExtensionalCardinality
          SetEqual
          (UnitPair reals S)
          pair-count
        and
        StrictLess reals
          (fromNat reals pair-count)
          (bound n))

putnam-1978-a6 : Set1
putnam-1978-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (powers : StandardRealPowers reals) ->
  Putnam1978A6Statement.proposition reals powers
