-- Statement-only formalization of PutnamBench corpus artifact putnam_1967_a3:
-- five is the least positive integer leading coefficient of a quadratic with
-- integer coefficients and two distinct real roots in (0, 1). This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor top

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

IntLessOrEqual : Int -> Int -> Set
IntLessOrEqual (pos m) (pos n) = m <=N n
IntLessOrEqual (pos m) (negsuc n) = Bottom
IntLessOrEqual (negsuc m) (pos n) = Top
IntLessOrEqual (negsuc m) (negsuc n) = n <=N m

data PositiveInteger : Int -> Set where
  positive : {n : Nat} -> PositiveInteger (pos (suc n))

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    oneR-not-zeroR :
      oneR != zeroR

    addR-commutative :
      (x y : R) -> addR x y == addR y x
    addR-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    addR-zero :
      (x : R) -> addR x zeroR == x
    addR-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiplyR-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiplyR-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiplyR-one :
      (x : R) -> multiplyR x oneR == x
    multiplyR-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverseR-zero :
      inverseR zeroR == zeroR
    multiplyR-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqualR x y or lessOrEqualR y x
    addR-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiplyR-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zeroR-less-than-oneR :
      lessOrEqualR zeroR oneR and zeroR != oneR

    fromNatR-zero :
      fromNatR zero == zeroR
    fromNatR-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNatR-addition :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNatR-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNatR-injective :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqualR x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

open CompleteOrderedRealField

integerToReal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
integerToReal reals (pos n) =
  fromNatR reals n
integerToReal reals (negsuc n) =
  negateR reals (fromNatR reals (suc n))

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqualR reals x y and x != y

record IntegerQuadratic : Set where
  constructor quadratic
  field
    constantCoefficient : Int
    linearCoefficient   : Int
    leadingCoefficient  : Int

open IntegerQuadratic

evaluateQuadratic :
  {R : Set} ->
  CompleteOrderedRealField R ->
  IntegerQuadratic ->
  R ->
  R
evaluateQuadratic reals polynomial x =
  addR reals
    (addR reals
      (multiplyR reals
        (integerToReal reals (leadingCoefficient polynomial))
        (multiplyR reals x x))
      (multiplyR reals
        (integerToReal reals (linearCoefficient polynomial))
        x))
    (integerToReal reals (constantCoefficient polynomial))

InOpenUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
InOpenUnitInterval reals x =
  StrictLess reals (zeroR reals) x
  and
  StrictLess reals x (oneR reals)

HasTwoDistinctUnitRoots :
  {R : Set} ->
  CompleteOrderedRealField R ->
  IntegerQuadratic ->
  Set
HasTwoDistinctUnitRoots {R} reals polynomial =
  Exists R
    (\ z1 ->
      Exists R
        (\ z2 ->
          InOpenUnitInterval reals z1
          and
          InOpenUnitInterval reals z2
          and
          z1 != z2
          and
          evaluateQuadratic reals polynomial z1 == zeroR reals
          and
          evaluateQuadratic reals polynomial z2 == zeroR reals))

QualifyingLeadingCoefficient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  Set
QualifyingLeadingCoefficient reals coefficient =
  PositiveInteger coefficient
  and
  Exists IntegerQuadratic
    (\ polynomial ->
      leadingCoefficient polynomial == coefficient
      and
      HasTwoDistinctUnitRoots reals polynomial)

IsLeastQualifyingCoefficient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  Set
IsLeastQualifyingCoefficient reals coefficient =
  QualifyingLeadingCoefficient reals coefficient
  and
  ((other : Int) ->
    QualifyingLeadingCoefficient reals other ->
    IntLessOrEqual coefficient other)

fiveN : Nat
fiveN = suc (suc (suc (suc (suc zero))))

fiveInt : Int
fiveInt = pos fiveN

putnam-1967-a3 : Set1
putnam-1967-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  IsLeastQualifyingCoefficient reals fiveInt
