-- Statement-only formalization of Thousand Theorems corpus artifact Q1243340,
-- "Birkhoff–Von Neumann theorem": over any linear ordered field and finite index
-- type, the doubly stochastic matrices are exactly the finite convex combinations
-- of permutation matrices. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1243340_birkhoff_von_neumann_theorem where

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
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
    equalIndex : I -> I -> Bool
    equalIndex-sound :
      (x y : I) ->
      equalIndex x y == true ->
      x == y
    equalIndex-complete :
      (x y : I) ->
      x == y ->
      equalIndex x y == true

open FiniteIndex

record LinearOrderedField
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set r

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
    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexive :
      (x : R) ->
      lessOrEqualR x x
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
    add-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-one :
      lessOrEqualR zeroR oneR and zeroR != oneR

open LinearOrderedField

Matrix :
  {i r : Level} ->
  Set i ->
  Set r ->
  Set (i ⊔ r)
Matrix I R =
  I -> I -> R

MatrixEqual :
  {i r : Level}
  {I : Set i}
  {R : Set r} ->
  Matrix I R ->
  Matrix I R ->
  Set (i ⊔ r)
MatrixEqual {I = I} A B =
  (row column : I) ->
  A row column == B row column

record Permutation
  {i : Level}
  (I : Set i) :
  Set (lsuc i) where

  field
    forwardPermutation : I -> I
    inversePermutation : I -> I
    forward-inverse :
      (x : I) ->
      forwardPermutation (inversePermutation x) == x
    inverse-forward :
      (x : I) ->
      inversePermutation (forwardPermutation x) == x

open Permutation

select :
  {a : Level}
  {A : Set a} ->
  Bool ->
  A ->
  A ->
  A
select false yes no = no
select true yes no = yes

permutationMatrix :
  {i r : Level}
  {I : Set i}
  {R : Set r} ->
  FiniteIndex I ->
  LinearOrderedField R ->
  Permutation I ->
  Matrix I R
permutationMatrix finite orderedField permutation row column =
  select
    (equalIndex finite
      (forwardPermutation permutation row)
      column)
    (oneR orderedField)
    (zeroR orderedField)

sumFin :
  {r : Level}
  {R : Set r} ->
  LinearOrderedField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin orderedField {zero} term =
  zeroR orderedField
sumFin orderedField {suc n} term =
  addR orderedField
    (term fzero)
    (sumFin orderedField (\ k -> term (fsuc k)))

sumIndex :
  {i r : Level}
  {I : Set i}
  {R : Set r} ->
  FiniteIndex I ->
  LinearOrderedField R ->
  (I -> R) ->
  R
sumIndex finite orderedField term =
  sumFin orderedField
    (\ k -> term (fromFin finite k))

record DoublyStochastic
  {i r : Level}
  {I : Set i}
  {R : Set r}
  (finite : FiniteIndex I)
  (orderedField : LinearOrderedField R)
  (matrix : Matrix I R) :
  Set (i ⊔ r) where

  field
    entries-nonnegative :
      (row column : I) ->
      lessOrEqualR orderedField
        (zeroR orderedField)
        (matrix row column)
    row-sums-one :
      (row : I) ->
      sumIndex finite orderedField (matrix row) ==
      oneR orderedField
    column-sums-one :
      (column : I) ->
      sumIndex finite orderedField
        (\ row -> matrix row column) ==
      oneR orderedField

record WeightedPermutation
  {i r : Level}
  (I : Set i)
  (R : Set r) :
  Set (lsuc i ⊔ r) where

  constructor weighted
  field
    coefficient : R
    permutation : Permutation I

open WeightedPermutation

data NonnegativeWeights
  {i r : Level}
  {I : Set i}
  {R : Set r}
  (orderedField : LinearOrderedField R) :
  List (WeightedPermutation I R) ->
  Set (lsuc i ⊔ r) where

  no-weights :
    NonnegativeWeights orderedField []
  nonnegative-cons :
    {term : WeightedPermutation I R}
    {terms : List (WeightedPermutation I R)} ->
    lessOrEqualR orderedField
      (zeroR orderedField)
      (coefficient term) ->
    NonnegativeWeights orderedField terms ->
    NonnegativeWeights orderedField (term ∷ terms)

weightSum :
  {i r : Level}
  {I : Set i}
  {R : Set r} ->
  LinearOrderedField R ->
  List (WeightedPermutation I R) ->
  R
weightSum orderedField [] =
  zeroR orderedField
weightSum orderedField (term ∷ terms) =
  addR orderedField
    (coefficient term)
    (weightSum orderedField terms)

weightedPermutationSum :
  {i r : Level}
  {I : Set i}
  {R : Set r} ->
  FiniteIndex I ->
  LinearOrderedField R ->
  List (WeightedPermutation I R) ->
  Matrix I R
weightedPermutationSum finite orderedField [] row column =
  zeroR orderedField
weightedPermutationSum finite orderedField (term ∷ terms) row column =
  addR orderedField
    (multiplyR orderedField
      (coefficient term)
      (permutationMatrix finite orderedField
        (permutation term)
        row
        column))
    (weightedPermutationSum finite orderedField terms row column)

ConvexCombinationOfPermutationMatrices :
  {i r : Level}
  {I : Set i}
  {R : Set r} ->
  FiniteIndex I ->
  LinearOrderedField R ->
  Matrix I R ->
  Set (lsuc i ⊔ r)
ConvexCombinationOfPermutationMatrices
    {I = I} {R = R} finite orderedField matrix =
  Exists
    (List (WeightedPermutation I R))
    (\ terms ->
      NonnegativeWeights orderedField terms and
      (weightSum orderedField terms == oneR orderedField and
      MatrixEqual
        (weightedPermutationSum finite orderedField terms)
        matrix))

birkhoff-von-neumann-theorem : Setω
birkhoff-von-neumann-theorem =
  {i r : Level} ->
  (I : Set i) ->
  (finite : FiniteIndex I) ->
  (R : Set r) ->
  (orderedField : LinearOrderedField R) ->
  (matrix : Matrix I R) ->
  Iff
    (DoublyStochastic finite orderedField matrix)
    (ConvexCombinationOfPermutationMatrices
      finite orderedField matrix)
