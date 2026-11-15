-- Statement-only formalization of PutnamBench corpus artifact putnam_1992_b6
-- (putnambench__agda__putnam_1992_b6): a set of real square matrices satisfying
-- exclusive signed closure and pairwise commutation up to sign has cardinality
-- at most n squared. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
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

Xor : Set -> Set -> Set
Xor A B =
  (A or B) and Not (A and B)

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Positive : Nat -> Set where
  positive : (n : Nat) -> Positive (suc n)

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

sameFin : {n : Nat} -> Fin n -> Fin n -> Bool
sameFin fzero fzero =
  true
sameFin fzero (fsuc j) =
  false
sameFin (fsuc i) fzero =
  false
sameFin (fsuc i) (fsuc j) =
  sameFin i j

ifBool : {A : Set} -> Bool -> A -> A -> A
ifBool true whenTrue whenFalse =
  whenTrue
ifBool false whenTrue whenFalse =
  whenFalse

Matrix : Set -> Nat -> Set
Matrix R n =
  Fin n -> Fin n -> R

MatrixEqual :
  {R : Set} {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Set
MatrixEqual {n = n} A B =
  (i j : Fin n) ->
  A i j == B i j

MatrixSetExtensional :
  {R : Set} {n : Nat} ->
  (Matrix R n -> Set) ->
  Set
MatrixSetExtensional M =
  (A B : _) ->
  MatrixEqual A B ->
  Iff (M A) (M B)

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

identityMatrix :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n
identityMatrix reals i j =
  ifBool
    (sameFin i j)
    (oneR reals)
    (zeroR reals)

matrixNegate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Matrix R n
matrixNegate reals A i j =
  negate reals (A i j)

matrixMultiply :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Matrix R n
matrixMultiply reals A B i j =
  sumFin reals
    (\ k -> multiply reals (A i k) (B k j))

record HasExtensionalCardinality
  {A : Set}
  (equivalent : A -> A -> Set)
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

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

CardinalityAtMost :
  {A : Set} ->
  (equivalent : A -> A -> Set) ->
  (member : A -> Set) ->
  Nat ->
  Set
CardinalityAtMost equivalent member bound =
  Exists Nat
    (\ cardinality ->
      HasExtensionalCardinality equivalent member cardinality
      and
      cardinality <=N bound)

putnam-1992-b6 : Set1
putnam-1992-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  Positive n ->
  (M : Matrix R n -> Set) ->
  MatrixSetExtensional M ->
  M (identityMatrix reals) ->
  ((A B : Matrix R n) ->
    M A ->
    M B ->
    Xor
      (M (matrixMultiply reals A B))
      (M (matrixMultiply reals (matrixNegate reals A) B))) ->
  ((A B : Matrix R n) ->
    M A ->
    M B ->
    MatrixEqual
      (matrixMultiply reals A B)
      (matrixMultiply reals B A)
    or
    MatrixEqual
      (matrixMultiply reals A B)
      (matrixMultiply reals (matrixNegate reals B) A)) ->
  ((A : Matrix R n) ->
    M A ->
    Not (MatrixEqual A (identityMatrix reals)) ->
    Exists (Matrix R n)
      (\ B ->
        M B
        and
        MatrixEqual
          (matrixMultiply reals A B)
          (matrixMultiply reals (matrixNegate reals B) A))) ->
  CardinalityAtMost MatrixEqual M (n * n)
