-- Statement-only formalization of PutnamBench corpus artifact putnam_1990_a4:
-- the least number of paper punches whose irrational-distance loci cover the
-- real plane is three. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1990A4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; _⊔_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  {ell : Level} ->
  Set ell ->
  Set ell
Not A =
  A -> Bottom

_!=_ :
  {ell : Level} ->
  {A : Set ell} ->
  A ->
  A ->
  Set ell
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
  (property : A -> Set property-level) :
  Set (element-level ⊔ property-level) where

  constructor witness
  field
    value     : A
    satisfies : property value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Predicate :
  Set ->
  Set1
Predicate A =
  A -> Set

record HasCardinality
  {A : Set}
  (S : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      S (enumerate index)
    enumeration-complete :
      (x : A) ->
      S x ->
      Exists (Fin cardinality)
        (\ index -> x == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
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
      (x y : R) ->
      add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) ->
      add x zeroR == x
    add-inverse :
      (x : R) ->
      add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) ->
      multiply x oneR == x
    multiply-zero :
      (x : R) ->
      multiply x zeroR == zeroR
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
      (x : R) ->
      lessOrEqual x x
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
        (\ n -> lessOrEqual x (fromNat n))
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

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

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

IsRational :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
IsRational reals x =
  Exists Int
    (\ numerator ->
      Exists Int
        (\ denominator ->
          denominator != pos zero
          and
          x ==
          divide reals
            (fromInt reals numerator)
            (fromInt reals denominator)))

Irrational :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Irrational reals x =
  Not (IsRational reals x)

PunchesEveryPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point R -> Set) ->
  Set
PunchesEveryPoint {R} reals centers =
  (Q : Point R) ->
  Exists (Point R)
    (\ P ->
      centers P
      and
      Irrational reals (distance reals P Q))

ConfigurationOfSize :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Set1
ConfigurationOfSize {R} reals cardinality =
  Exists (Predicate (Point R))
    (\ centers ->
      HasCardinality centers cardinality
      and
      PunchesEveryPoint reals centers)

record IsLeastConfigurationSize
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (least : Nat) :
  Set1 where

  field
    attainable :
      ConfigurationOfSize reals least
    lower-bound :
      (cardinality : Nat) ->
      ConfigurationOfSize reals cardinality ->
      least <=N cardinality

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

putnam-1990-a4 : Set1
putnam-1990-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  IsLeastConfigurationSize reals three
