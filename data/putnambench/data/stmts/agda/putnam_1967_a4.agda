-- Statement-only formalization of PutnamBench corpus artifact putnam_1967_a4:
-- for lambda greater than one half, no integrable real function satisfies the
-- stated nonlinear interval-integral equation on [0, 1]. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1967A4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_
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

record Iff (A B : Set) : Set where
  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

NatStrictLess : Nat -> Nat -> Set
NatStrictLess m n =
  suc m <=N n

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

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  addR reals x (negateR reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiplyR reals x (inverseR reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqualR reals x y and x != y

ClosedInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
ClosedInterval reals lower upper x =
  lessOrEqualR reals lower x
  and
  lessOrEqualR reals x upper

OpenInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
OpenInterval reals lower upper x =
  StrictLess reals lower x
  and
  StrictLess reals x upper

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (addR reals center radius)

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  addR reals
    (sumFirst reals n term)
    (term n)

TaggedPartition :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Nat ->
  (Nat -> R) ->
  (Nat -> R) ->
  Set
TaggedPartition reals lower upper pieces points tags =
  NatStrictLess zero pieces
  and
  points zero == lower
  and
  points pieces == upper
  and
  ((i : Nat) ->
    NatStrictLess i pieces ->
    lessOrEqualR reals (points i) (points (suc i)))
  and
  ((i : Nat) ->
    NatStrictLess i pieces ->
    ClosedInterval reals
      (points i)
      (points (suc i))
      (tags i))

MeshBelow :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R ->
  Set
MeshBelow reals pieces points bound =
  (i : Nat) ->
  NatStrictLess i pieces ->
  StrictLess reals
    (subtract reals (points (suc i)) (points i))
    bound

taggedRiemannSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  (Nat -> R) ->
  (R -> R) ->
  R
taggedRiemannSum reals pieces points tags function =
  sumFirst reals pieces
    (\ i ->
      multiplyR reals
        (function (tags i))
        (subtract reals
          (points (suc i))
          (points i)))

RiemannIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  R ->
  Set
RiemannIntegralValue {R} reals lower upper function value =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((pieces : Nat) ->
        (points tags : Nat -> R) ->
        TaggedPartition reals
          lower upper pieces points tags ->
        MeshBelow reals pieces points delta ->
        CloseTo reals value epsilon
          (taggedRiemannSum reals
            pieces points tags function)))

RiemannIntegrableOn :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  Set
RiemannIntegrableOn reals lower upper function =
  Exists _
    (RiemannIntegralValue reals lower upper function)

two :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
two reals =
  fromNatR reals (suc (suc zero))

half :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
half reals =
  divide reals (oneR reals) (two reals)

module Putnam1967A4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set
  proposition =
    (lambda : R) ->
    StrictLess reals (half reals) lambda ->
    Not
      (Exists (R -> R)
        (\ u ->
          RiemannIntegrableOn reals
            (zeroR reals)
            (oneR reals)
            u
          and
          ((x : R) ->
            ClosedInterval reals (zeroR reals) (oneR reals) x ->
            Exists R
              (\ integralValue ->
                RiemannIntegralValue reals
                  x
                  (oneR reals)
                  (\ y ->
                    multiplyR reals
                      (u y)
                      (u (subtract reals y x)))
                  integralValue
                and
                u x ==
                addR reals
                  (oneR reals)
                  (multiplyR reals lambda integralValue)))))

putnam-1967-a4 : Set1
putnam-1967-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1967A4Statement.proposition reals
