-- Statement-only formalization of PutnamBench corpus artifact putnam_1969_b6:
-- real rectangular matrices A and B whose product is the specified 3 by 3
-- matrix have reverse product equal to 9 times the 2 by 2 identity matrix.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
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

fourN : Nat
fourN =
  suc threeN

fiveN : Nat
fiveN =
  suc fourN

sixN : Nat
sixN =
  suc fiveN

sevenN : Nat
sevenN =
  suc sixN

eightN : Nat
eightN =
  suc sevenN

nineN : Nat
nineN =
  suc eightN

index0of2 : Fin twoN
index0of2 =
  fzero

index1of2 : Fin twoN
index1of2 =
  fsuc fzero

index0of3 : Fin threeN
index0of3 =
  fzero

index1of3 : Fin threeN
index1of3 =
  fsuc fzero

index2of3 : Fin threeN
index2of3 =
  fsuc (fsuc fzero)

Matrix :
  Set ->
  Nat ->
  Nat ->
  Set
Matrix R rows columns =
  Fin rows -> Fin columns -> R

MatrixEqual :
  {R : Set} {rows columns : Nat} ->
  Matrix R rows columns ->
  Matrix R rows columns ->
  Set
MatrixEqual {rows = rows} {columns = columns} A B =
  (i : Fin rows) ->
  (j : Fin columns) ->
  A i j == B i j

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} term =
  zeroR reals
sumFin reals {suc n} term =
  add reals
    (term fzero)
    (sumFin reals (\ i -> term (fsuc i)))

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

nineIdentity :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix R twoN twoN
nineIdentity reals fzero fzero =
  fromNat reals nineN
nineIdentity reals fzero (fsuc fzero) =
  zeroR reals
nineIdentity reals (fsuc fzero) fzero =
  zeroR reals
nineIdentity reals (fsuc fzero) (fsuc fzero) =
  fromNat reals nineN

SpecifiedProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Matrix R threeN threeN ->
  Set
SpecifiedProduct reals p =
  p index0of3 index0of3 == fromNat reals eightN
  and
  p index0of3 index1of3 == fromNat reals twoN
  and
  p index0of3 index2of3 == negate reals (fromNat reals twoN)
  and
  p index1of3 index0of3 == fromNat reals twoN
  and
  p index1of3 index1of3 == fromNat reals fiveN
  and
  p index1of3 index2of3 == fromNat reals fourN
  and
  p index2of3 index0of3 == negate reals (fromNat reals twoN)
  and
  p index2of3 index1of3 == fromNat reals fourN
  and
  p index2of3 index2of3 == fromNat reals fiveN

putnam-1969-b6 : Set1
putnam-1969-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (A : Matrix R threeN twoN) ->
  (B : Matrix R twoN threeN) ->
  (p : Matrix R threeN threeN) ->
  SpecifiedProduct reals p ->
  MatrixEqual (matrixMultiply reals A B) p ->
  MatrixEqual
    (matrixMultiply reals B A)
    (nineIdentity reals)
