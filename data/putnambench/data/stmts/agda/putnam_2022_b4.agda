-- Statement-only formalization of PutnamBench corpus artifact putnam_2022_b4
-- (putnambench__agda__putnam_2022_b4): classification of cyclic sequences of
-- distinct real numbers whose consecutive triples form three-term arithmetic
-- progressions. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2022B4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

fourN : Nat
fourN =
  suc threeN

nineN : Nat
nineN =
  suc (suc (suc (suc (suc fourN))))

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

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

SameThreeElementSet :
  {R : Set} ->
  R ->
  R ->
  R ->
  R ->
  R ->
  R ->
  Set
SameThreeElementSet x0 x1 x2 y0 y1 y2 =
  (z : _) ->
  Iff
    ((z == x0) or ((z == x1) or (z == x2)))
    ((z == y0) or ((z == y1) or (z == y2)))

ThreeTermArithmeticProgression :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
ThreeTermArithmeticProgression {R} reals x0 x1 x2 =
  (o0 o1 o2 : R) ->
  (StrictLess reals o0 o1
    and
    (StrictLess reals o1 o2
      and
      SameThreeElementSet o0 o1 o2 x0 x1 x2)) ->
  subtract reals o1 o0 == subtract reals o2 o1

record CyclicProgression
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (n : Nat)
  (x : Nat -> R) :
  Set where

  field
    distinct :
      (i j : Fin n) ->
      finToNat i != finToNat j ->
      x (finToNat i) != x (finToNat j)

    consecutive-triples :
      (i : Fin n) ->
      ThreeTermArithmeticProgression reals
        (x (finToNat i))
        (x (naturalMod (finToNat i + oneN) n))
        (x (naturalMod (finToNat i + twoN) n))

Divides : Nat -> Nat -> Set
Divides divisor number =
  Exists Nat
    (\ quotient -> divisor * quotient == number)

putnam-2022-b4-solution : Nat -> Set
putnam-2022-b4-solution n =
  Divides threeN n and nineN <=N n

putnam-2022-b4 : Set1
putnam-2022-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  fourN <=N n ->
  Iff
    (Exists (Nat -> R)
      (\ x -> CyclicProgression reals n x))
    (putnam-2022-b4-solution n)
