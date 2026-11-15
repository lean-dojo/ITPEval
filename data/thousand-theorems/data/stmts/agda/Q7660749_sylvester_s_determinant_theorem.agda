-- Statement-only formalization of Thousand Theorems corpus artifact Q7660749,
-- "Sylvester's determinant theorem": over a commutative ring, for rectangular
-- matrices A and B indexed by arbitrary finite types, det(I + AB) equals
-- det(I + BA). This file contains no proof.

{-# OPTIONS --safe #-}

module Q7660749_sylvester_s_determinant_theorem where

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

record RingOperations
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR : R -> R

open RingOperations

record CommutativeRing
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    operations : RingOperations R

    add-commutative :
      (x y : R) ->
      addR operations x y == addR operations y x
    add-associative :
      (x y z : R) ->
      addR operations (addR operations x y) z ==
      addR operations x (addR operations y z)
    add-zero :
      (x : R) ->
      addR operations x (zeroR operations) == x
    add-inverse :
      (x : R) ->
      addR operations x (negateR operations x) ==
      zeroR operations

    multiply-commutative :
      (x y : R) ->
      multiplyR operations x y == multiplyR operations y x
    multiply-associative :
      (x y z : R) ->
      multiplyR operations (multiplyR operations x y) z ==
      multiplyR operations x (multiplyR operations y z)
    multiply-one :
      (x : R) ->
      multiplyR operations x (oneR operations) == x
    distribute :
      (x y z : R) ->
      multiplyR operations x (addR operations y z) ==
      addR operations
        (multiplyR operations x y)
        (multiplyR operations x z)

open CommutativeRing

Matrix :
  {i j r : Level} ->
  Set i ->
  Set j ->
  Set r ->
  Set (i ⊔ j ⊔ r)
Matrix I J R =
  I -> J -> R

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
  RingOperations R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin operations {zero} term =
  zeroR operations
sumFin operations {suc n} term =
  addR operations
    (term fzero)
    (sumFin operations (λ k -> term (fsuc k)))

sumIndex :
  {i r : Level} ->
  {I : Set i} ->
  {R : Set r} ->
  FiniteIndex I ->
  RingOperations R ->
  (I -> R) ->
  R
sumIndex finite operations term =
  sumFin operations (λ k -> term (fromFin finite k))

identityMatrix :
  {i r : Level} ->
  {I : Set i} ->
  {R : Set r} ->
  FiniteIndex I ->
  RingOperations R ->
  Matrix I I R
identityMatrix finite operations row column =
  select
    (finEqual (toFin finite row) (toFin finite column))
    (oneR operations)
    (zeroR operations)

matrixAdd :
  {i j r : Level} ->
  {I : Set i} ->
  {J : Set j} ->
  {R : Set r} ->
  RingOperations R ->
  Matrix I J R ->
  Matrix I J R ->
  Matrix I J R
matrixAdd operations A B row column =
  addR operations (A row column) (B row column)

matrixMultiply :
  {i j k r : Level} ->
  {I : Set i} ->
  {J : Set j} ->
  {K : Set k} ->
  {R : Set r} ->
  FiniteIndex K ->
  RingOperations R ->
  Matrix I K R ->
  Matrix K J R ->
  Matrix I J R
matrixMultiply finite operations A B row column =
  sumIndex finite operations
    (λ middle ->
      multiplyR operations
        (A row middle)
        (B middle column))

reindexSquare :
  {i r : Level} ->
  {I : Set i} ->
  {R : Set r} ->
  (finite : FiniteIndex I) ->
  Matrix I I R ->
  Matrix (Fin (size finite)) (Fin (size finite)) R
reindexSquare finite A row column =
  A (fromFin finite row) (fromFin finite column)

skip :
  {n : Nat} ->
  Fin (suc n) ->
  Fin n ->
  Fin (suc n)
skip {zero} column ()
skip {suc n} fzero k =
  fsuc k
skip {suc n} (fsuc column) fzero =
  fzero
skip {suc n} (fsuc column) (fsuc k) =
  fsuc (skip column k)

firstRowMinor :
  {r : Level} ->
  {R : Set r} ->
  {n : Nat} ->
  Matrix (Fin (suc n)) (Fin (suc n)) R ->
  Fin (suc n) ->
  Matrix (Fin n) (Fin n) R
firstRowMinor A column row minor-column =
  A (fsuc row) (skip column minor-column)

alternatingSign :
  {r : Level} ->
  {R : Set r} ->
  RingOperations R ->
  {n : Nat} ->
  Fin n ->
  R
alternatingSign operations fzero =
  oneR operations
alternatingSign operations (fsuc i) =
  negateR operations (alternatingSign operations i)

determinantFin :
  {r : Level} ->
  {R : Set r} ->
  RingOperations R ->
  {n : Nat} ->
  Matrix (Fin n) (Fin n) R ->
  R
determinantFin operations {zero} A =
  oneR operations
determinantFin operations {suc n} A =
  sumFin operations
    (λ column ->
      multiplyR operations
        (alternatingSign operations column)
        (multiplyR operations
          (A fzero column)
          (determinantFin operations
            (firstRowMinor A column))))

determinant :
  {i r : Level} ->
  {I : Set i} ->
  {R : Set r} ->
  RingOperations R ->
  (finite : FiniteIndex I) ->
  Matrix I I R ->
  R
determinant operations finite A =
  determinantFin operations (reindexSquare finite A)

sylvesters-determinant-theorem : Setω
sylvesters-determinant-theorem =
  {m n r : Level} ->
  (M : Set m) ->
  (finiteM : FiniteIndex M) ->
  (N : Set n) ->
  (finiteN : FiniteIndex N) ->
  (R : Set r) ->
  (ring : CommutativeRing R) ->
  (A : Matrix M N R) ->
  (B : Matrix N M R) ->
  determinant (operations ring) finiteM
    (matrixAdd (operations ring)
      (identityMatrix finiteM (operations ring))
      (matrixMultiply finiteN (operations ring) A B))
  ==
  determinant (operations ring) finiteN
    (matrixAdd (operations ring)
      (identityMatrix finiteN (operations ring))
      (matrixMultiply finiteM (operations ring) B A))
