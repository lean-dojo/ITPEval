-- Statement-only formalization of PutnamBench corpus artifact putnam_2015_b3
-- (putnambench__agda__putnam_2015_b3): classification of real 2 by 2 matrices
-- whose entries and the entries of some power above one are arithmetic
-- progressions. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2015B3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
infixr 2 _or_ _iff_

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

record _iff_ (A B : Set) : Set where
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

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

record Matrix2 (R : Set) : Set where
  constructor matrix
  field
    entry00 : R
    entry01 : R
    entry10 : R
    entry11 : R

open Matrix2

matrixMultiply :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix2 R ->
  Matrix2 R ->
  Matrix2 R
matrixMultiply reals A B =
  matrix
    (add reals
      (multiply reals (entry00 A) (entry00 B))
      (multiply reals (entry01 A) (entry10 B)))
    (add reals
      (multiply reals (entry00 A) (entry01 B))
      (multiply reals (entry01 A) (entry11 B)))
    (add reals
      (multiply reals (entry10 A) (entry00 B))
      (multiply reals (entry11 A) (entry10 B)))
    (add reals
      (multiply reals (entry10 A) (entry01 B))
      (multiply reals (entry11 A) (entry11 B)))

identityMatrix :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix2 R
identityMatrix reals =
  matrix
    (oneR reals)
    (zeroR reals)
    (zeroR reals)
    (oneR reals)

matrixPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix2 R ->
  Nat ->
  Matrix2 R
matrixPower reals M zero =
  identityMatrix reals
matrixPower reals M (suc exponent) =
  matrixMultiply reals
    (matrixPower reals M exponent)
    M

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

ArithmeticProgression :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix2 R ->
  Set
ArithmeticProgression reals M =
  subtract reals (entry01 M) (entry00 M) ==
    subtract reals (entry10 M) (entry01 M)
  and
  subtract reals (entry10 M) (entry01 M) ==
    subtract reals (entry11 M) (entry10 M)

ConstantFamily :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix2 R ->
  Set
ConstantFamily {R} reals M =
  Exists R
    (\ alpha ->
      entry00 M == multiply reals alpha (oneR reals)
      and
      entry01 M == multiply reals alpha (oneR reals)
      and
      entry10 M == multiply reals alpha (oneR reals)
      and
      entry11 M == multiply reals alpha (oneR reals))

AlternatingFamily :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix2 R ->
  Set
AlternatingFamily {R} reals M =
  Exists R
    (\ beta ->
      entry00 M ==
        multiply reals beta
          (negate reals (fromNat reals threeN))
      and
      entry01 M ==
        multiply reals beta
          (negate reals (oneR reals))
      and
      entry10 M ==
        multiply reals beta (oneR reals)
      and
      entry11 M ==
        multiply reals beta (fromNat reals threeN))

SolutionFamily :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix2 R ->
  Set
SolutionFamily reals M =
  ConstantFamily reals M
  or
  AlternatingFamily reals M

HasLaterArithmeticPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix2 R ->
  Set
HasLaterArithmeticPower reals M =
  Exists Nat
    (\ exponent ->
      oneN <N exponent
      and
      ArithmeticProgression reals
        (matrixPower reals M exponent))

Putnam2015B3 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Set
Putnam2015B3 {R} reals =
  (M : Matrix2 R) ->
  (ArithmeticProgression reals M
    and
    HasLaterArithmeticPower reals M)
  iff
  SolutionFamily reals M

putnam-2015-b3 : Set1
putnam-2015-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2015B3 reals
