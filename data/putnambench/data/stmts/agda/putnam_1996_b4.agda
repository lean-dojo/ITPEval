-- Statement-only formalization of PutnamBench corpus artifact putnam_1996_b4
-- (putnambench__agda__putnam_1996_b4): no real 2 by 2 matrix has matrix sine
-- equal to the matrix with rows (1, 1996) and (0, 1). This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

open CompleteOrderedRealField

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

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
    (add reals center radius)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

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

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

alternatingPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
alternatingPower reals n =
  naturalPower reals
    (negate reals (oneR reals))
    n

Matrix :
  Set ->
  Nat ->
  Nat ->
  Set
Matrix R rows columns =
  Fin rows -> Fin columns -> R

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} terms =
  zeroR reals
sumFin reals {suc n} terms =
  add reals
    (terms fzero)
    (sumFin reals (\ i -> terms (fsuc i)))

matrixMultiply :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {rows middle columns : Nat} ->
  Matrix R rows middle ->
  Matrix R middle columns ->
  Matrix R rows columns
matrixMultiply reals A B i j =
  sumFin reals
    (\ k -> multiply reals (A i k) (B k j))

identityTwo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix R twoN twoN
identityTwo reals fzero fzero =
  oneR reals
identityTwo reals fzero (fsuc fzero) =
  zeroR reals
identityTwo reals (fsuc fzero) fzero =
  zeroR reals
identityTwo reals (fsuc fzero) (fsuc fzero) =
  oneR reals

matrixPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix R twoN twoN ->
  Nat ->
  Matrix R twoN twoN
matrixPower reals A zero =
  identityTwo reals
matrixPower reals A (suc n) =
  matrixMultiply reals A (matrixPower reals A n)

matrixSineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix R twoN twoN ->
  Fin twoN ->
  Fin twoN ->
  Nat ->
  R
matrixSineTerm reals A i j n =
  divide reals
    (multiply reals
      (alternatingPower reals n)
      (matrixPower reals A (suc (twoN * n)) i j))
    (fromNat reals (factorial (suc (twoN * n))))

targetMatrix :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix R twoN twoN
targetMatrix reals fzero fzero =
  oneR reals
targetMatrix reals fzero (fsuc fzero) =
  fromNat reals 1996
targetMatrix reals (fsuc fzero) fzero =
  zeroR reals
targetMatrix reals (fsuc fzero) (fsuc fzero) =
  oneR reals

MatrixSineEqualsTarget :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix R twoN twoN ->
  Set
MatrixSineEqualsTarget reals A =
  (i j : Fin twoN) ->
  SeriesHasSum reals
    (matrixSineTerm reals A i j)
    (targetMatrix reals i j)

putnam-1996-b4-solution : Set
putnam-1996-b4-solution =
  Bottom

putnam-1996-b4 : Set1
putnam-1996-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Iff
    (Exists (Matrix R twoN twoN)
      (MatrixSineEqualsTarget reals))
    putnam-1996-b4-solution
