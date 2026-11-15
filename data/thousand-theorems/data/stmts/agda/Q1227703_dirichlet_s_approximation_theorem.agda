-- Statement-only formalization of thousand-theorems corpus artifact Q1227703,
-- "Dirichlet's approximation theorem": every point of a real additive circle
-- of positive circumference T has, for each positive n, a multiple indexed
-- from 1 through n whose circle norm is at most T / (n + 1), expressed using
-- a real representative modulo integer multiples of T. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1227703_dirichlet_s_approximation_theorem where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Int using (Int; pos; negsuc)

infix 4 _!=_ _<=N_ _<N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR absoluteR : R -> R
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

    absolute-nonnegative :
      (x : R) ->
      lessThanR zeroR (absoluteR x) or absoluteR x == zeroR
    absolute-of-nonnegative :
      (x : R) ->
      (lessThanR zeroR x or zeroR == x) ->
      absoluteR x == x
    absolute-of-nonpositive :
      (x : R) ->
      (lessThanR x zeroR or x == zeroR) ->
      absoluteR x == negateR x
    absolute-zero-only :
      (x : R) ->
      absoluteR x == zeroR ->
      x == zeroR
    absolute-negate :
      (x : R) ->
      absoluteR (negateR x) == absoluteR x
    absolute-multiply :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)
    absolute-triangle :
      (x y : R) ->
      lessThanR (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y)) or
      absoluteR (addR x y) ==
        addR (absoluteR x) (absoluteR y)

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
    forward-absoluteR :
      (x : R) ->
      forwardR (absoluteR source x) ==
      absoluteR target (forwardR x)
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

CircleNormAtMost :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CircleNormAtMost {R = R} reals T representative bound =
  Exists Int
    (\ periodShift ->
      LessOrEqual reals
        (absoluteR reals
          (subtractR reals representative
            (multiplyR reals
              (fromIntR reals periodShift)
              T)))
        bound)

dirichlet-s-approximation-theorem : Set2
dirichlet-s-approximation-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (T : R) ->
  lessThanR reals (zeroR reals) T ->
  (representative : R) ->
  (n : Nat) ->
  zero <N n ->
  Exists Nat
    (\ j ->
      (suc zero <=N j)
      and
      ((j <=N n)
      and
      CircleNormAtMost reals T
        (multiplyR reals
          (fromNatR reals j)
          representative)
        (divideR reals T (fromNatR reals (suc n)))))
