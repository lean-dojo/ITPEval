-- Statement-only formalization of Thousand Theorems corpus artifact Q1551745,
-- "Binomial inverse theorem": for finite-indexed matrices over a ring, the
-- inverse of A + UCV has the standard binomial inverse form under the stated
-- invertibility assumptions. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1551745_binomial_inverse_theorem where

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record FiniteIndex
  {i : Level}
  (I : Set i) :
  Set (lsuc i) where

  field
    size : Nat
    toFin : I -> Fin size
    fromFin : Fin size -> I
    to-from :
      (k : Fin size) ->
      toFin (fromFin k) == k
    from-to :
      (x : I) ->
      fromFin (toFin x) == x

open FiniteIndex

record Ring
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR : R -> R

    add-associative :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-commutative :
      (x y : R) ->
      addR x y == addR y x
    add-zero :
      (x : R) ->
      addR x zeroR == x
    add-inverse :
      (x : R) ->
      addR x (negateR x) == zeroR

    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-one-left :
      (x : R) ->
      multiplyR oneR x == x
    multiply-one-right :
      (x : R) ->
      multiplyR x oneR == x

    distribute-left :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : R) ->
      multiplyR (addR x y) z ==
      addR (multiplyR x z) (multiplyR y z)

open Ring

Matrix :
  {i j r : Level} ->
  Set i ->
  Set j ->
  Set r ->
  Set (i ⊔ j ⊔ r)
Matrix I J R =
  I -> J -> R

MatrixEqual :
  {i j r : Level} ->
  {I : Set i} ->
  {J : Set j} ->
  {R : Set r} ->
  Matrix I J R ->
  Matrix I J R ->
  Set (i ⊔ j ⊔ r)
MatrixEqual {I = I} {J = J} A B =
  (row : I) ->
  (column : J) ->
  A row column == B row column

finEqual :
  {n : Nat} ->
  Fin n ->
  Fin n ->
  Bool
finEqual fzero fzero =
  true
finEqual fzero (fsuc j) =
  false
finEqual (fsuc i) fzero =
  false
finEqual (fsuc i) (fsuc j) =
  finEqual i j

select :
  {a : Level} ->
  {A : Set a} ->
  Bool ->
  A ->
  A ->
  A
select true yes no =
  yes
select false yes no =
  no

sumFin :
  {r : Level} ->
  {R : Set r} ->
  Ring R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin ring {zero} term =
  zeroR ring
sumFin ring {suc n} term =
  addR ring
    (term fzero)
    (sumFin ring (\ k -> term (fsuc k)))

sumIndex :
  {i r : Level} ->
  {I : Set i} ->
  {R : Set r} ->
  FiniteIndex I ->
  Ring R ->
  (I -> R) ->
  R
sumIndex finite ring term =
  sumFin ring (\ k -> term (fromFin finite k))

identityMatrix :
  {i r : Level} ->
  {I : Set i} ->
  {R : Set r} ->
  FiniteIndex I ->
  Ring R ->
  Matrix I I R
identityMatrix finite ring row column =
  select
    (finEqual (toFin finite row) (toFin finite column))
    (oneR ring)
    (zeroR ring)

matrixAdd :
  {i j r : Level} ->
  {I : Set i} ->
  {J : Set j} ->
  {R : Set r} ->
  Ring R ->
  Matrix I J R ->
  Matrix I J R ->
  Matrix I J R
matrixAdd ring A B row column =
  addR ring (A row column) (B row column)

matrixNegate :
  {i j r : Level} ->
  {I : Set i} ->
  {J : Set j} ->
  {R : Set r} ->
  Ring R ->
  Matrix I J R ->
  Matrix I J R
matrixNegate ring A row column =
  negateR ring (A row column)

matrixSubtract :
  {i j r : Level} ->
  {I : Set i} ->
  {J : Set j} ->
  {R : Set r} ->
  Ring R ->
  Matrix I J R ->
  Matrix I J R ->
  Matrix I J R
matrixSubtract ring A B =
  matrixAdd ring A (matrixNegate ring B)

matrixMultiply :
  {i j k r : Level} ->
  {I : Set i} ->
  {J : Set j} ->
  {K : Set k} ->
  {R : Set r} ->
  FiniteIndex K ->
  Ring R ->
  Matrix I K R ->
  Matrix K J R ->
  Matrix I J R
matrixMultiply finite ring A B row column =
  sumIndex finite ring
    (\ middle ->
      multiplyR ring
        (A row middle)
        (B middle column))

record Invertible
  {i r : Level}
  {I : Set i}
  {R : Set r}
  (finite : FiniteIndex I)
  (ring : Ring R)
  (A : Matrix I I R) :
  Set (lsuc (i ⊔ r)) where

  field
    inverse : Matrix I I R
    inverse-multiply :
      MatrixEqual
        (matrixMultiply finite ring inverse A)
        (identityMatrix finite ring)
    multiply-inverse :
      MatrixEqual
        (matrixMultiply finite ring A inverse)
        (identityMatrix finite ring)

open Invertible

binomialSum :
  {n m r : Level} ->
  {N : Set n} ->
  {M : Set m} ->
  {R : Set r} ->
  FiniteIndex M ->
  Ring R ->
  Matrix N N R ->
  Matrix N M R ->
  Matrix M M R ->
  Matrix M N R ->
  Matrix N N R
binomialSum finiteM ring A U C V =
  matrixAdd ring A
    (matrixMultiply finiteM ring
      (matrixMultiply finiteM ring U C)
      V)

binomialAuxiliary :
  {n m r : Level} ->
  {N : Set n} ->
  {M : Set m} ->
  {R : Set r} ->
  FiniteIndex N ->
  FiniteIndex M ->
  Ring R ->
  Matrix N N R ->
  Matrix N M R ->
  Matrix M M R ->
  Matrix M N R ->
  Matrix N N R ->
  Matrix M M R
binomialAuxiliary finiteN finiteM ring A U C V inverseA =
  matrixAdd ring C
    (matrixMultiply finiteM ring
      (matrixMultiply finiteN ring
        (matrixMultiply finiteN ring
          (matrixMultiply finiteM ring C V)
          inverseA)
        U)
      C)

binomialCorrection :
  {n m r : Level} ->
  {N : Set n} ->
  {M : Set m} ->
  {R : Set r} ->
  FiniteIndex N ->
  FiniteIndex M ->
  Ring R ->
  Matrix N N R ->
  Matrix N M R ->
  Matrix M M R ->
  Matrix M M R ->
  Matrix M N R ->
  Matrix N N R
binomialCorrection finiteN finiteM ring inverseA U C inverseAuxiliary V =
  matrixMultiply finiteN ring
    (matrixMultiply finiteM ring
      (matrixMultiply finiteM ring
        (matrixMultiply finiteM ring
          (matrixMultiply finiteM ring
            (matrixMultiply finiteN ring inverseA U)
            C)
          inverseAuxiliary)
        C)
      V)
    inverseA

binomialInverseExpression :
  {n m r : Level} ->
  {N : Set n} ->
  {M : Set m} ->
  {R : Set r} ->
  FiniteIndex N ->
  FiniteIndex M ->
  Ring R ->
  Matrix N N R ->
  Matrix N M R ->
  Matrix M M R ->
  Matrix M M R ->
  Matrix M N R ->
  Matrix N N R
binomialInverseExpression finiteN finiteM ring inverseA U C inverseAuxiliary V =
  matrixSubtract ring inverseA
    (binomialCorrection
      finiteN finiteM ring inverseA U C inverseAuxiliary V)

binomial-inverse-theorem : Setω
binomial-inverse-theorem =
  {n m r : Level} ->
  (N : Set n) ->
  (finiteN : FiniteIndex N) ->
  (M : Set m) ->
  (finiteM : FiniteIndex M) ->
  (R : Set r) ->
  (ring : Ring R) ->
  (A : Matrix N N R) ->
  (U : Matrix N M R) ->
  (C : Matrix M M R) ->
  (V : Matrix M N R) ->
  (invertibleA : Invertible finiteN ring A) ->
  (invertibleAuxiliary :
    Invertible finiteM ring
      (binomialAuxiliary
        finiteN finiteM ring A U C V
        (inverse invertibleA))) ->
  (invertibleSum :
    Invertible finiteN ring
      (binomialSum finiteM ring A U C V)) ->
  MatrixEqual
    (inverse invertibleSum)
    (binomialInverseExpression
      finiteN finiteM ring
      (inverse invertibleA)
      U C
      (inverse invertibleAuxiliary)
      V)
