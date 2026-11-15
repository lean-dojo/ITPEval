-- Statement-only formalization of PutnamBench corpus artifact putnam_1977_b3:
-- the universal claim that iterating the specified componentwise balancing
-- map eventually balances every positive irrational unit-sum triple is false.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

    strict-order-decidable :
      (x y : R) ->
      (lessOrEqual x y and x != y)
      or
      Not (lessOrEqual x y and x != y)

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

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

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

record Triple (R : Set) : Set where
  constructor triple
  field
    first-coordinate  : R
    second-coordinate : R
    third-coordinate  : R

open Triple

twoN : Nat
twoN =
  suc (suc zero)

oneHalf :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
oneHalf reals =
  divide reals
    (oneR reals)
    (fromNat reals twoN)

PositiveIrrationalUnitTriple :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Triple R ->
  Set
PositiveIrrationalUnitTriple reals t =
  Irrational reals (first-coordinate t)
  and
  Irrational reals (second-coordinate t)
  and
  Irrational reals (third-coordinate t)
  and
  StrictLess reals (zeroR reals) (first-coordinate t)
  and
  StrictLess reals (zeroR reals) (second-coordinate t)
  and
  StrictLess reals (zeroR reals) (third-coordinate t)
  and
  add reals
    (add reals (first-coordinate t) (second-coordinate t))
    (third-coordinate t)
    ==
    oneR reals

Balanced :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Triple R ->
  Set
Balanced reals t =
  StrictLess reals (first-coordinate t) (oneHalf reals)
  and
  StrictLess reals (second-coordinate t) (oneHalf reals)
  and
  StrictLess reals (third-coordinate t) (oneHalf reals)

balanceCoordinate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
balanceCoordinate reals x
  with strict-order-decidable reals (oneHalf reals) x
... | left _ =
  add reals
    (multiply reals (fromNat reals twoN) x)
    (negate reals (oneR reals))
... | right _ =
  multiply reals (fromNat reals twoN) x

balancingAct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Triple R ->
  Triple R
balancingAct reals t =
  triple
    (balanceCoordinate reals (first-coordinate t))
    (balanceCoordinate reals (second-coordinate t))
    (balanceCoordinate reals (third-coordinate t))

iterate :
  {A : Set} ->
  (A -> A) ->
  Nat ->
  A ->
  A
iterate f zero x =
  x
iterate f (suc n) x =
  iterate f n (f x)

EventuallyBalanced :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Set
EventuallyBalanced {R} reals =
  (t : Triple R) ->
  PositiveIrrationalUnitTriple reals t ->
  Exists Nat
    (\ n ->
      Balanced reals
        (iterate (balancingAct reals) n t))

Equivalent : Set -> Set -> Set
Equivalent A B =
  (A -> B) and (B -> A)

putnam-1977-b3-solution : Set
putnam-1977-b3-solution =
  Bottom

putnam-1977-b3 : Set1
putnam-1977-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Equivalent
    (EventuallyBalanced reals)
    putnam-1977-b3-solution
