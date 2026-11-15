-- Statement-only formalization of Thousand Theorems corpus artifact Q978688,
-- "Gershgorin circle theorem": every eigenvalue of a square matrix over an
-- arbitrary normed field lies within the norm bound centered at some diagonal
-- entry whose radius is the sum of the norms of the off-diagonal entries in
-- that row.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q978688_gershgorin_circle_theorem where

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

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

record Both
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> Either A B
  right : B -> Either A B

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

record CompleteOrderedField
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR : R -> R
    lessOrEqualR : R -> R -> Set r
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) ->
      addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) ->
      addR x zeroR == x
    add-inverseR :
      (x : R) ->
      addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) ->
      multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) ->
      multiplyR x oneR == x
    multiply-zeroR :
      (x : R) ->
      multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexiveR :
      (x : R) ->
      lessOrEqualR x x
    order-transitiveR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-totalR :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-orderR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat (λ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set r) ->
      Exists R P ->
      Exists R
        (λ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (λ supremum ->
          Both
            ((x : R) ->
              P x ->
              lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) ->
                P x ->
                lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

record Field
  {k : Level}
  (K : Set k) :
  Set (lsuc k) where

  field
    zeroK oneK : K
    addK multiplyK : K -> K -> K
    negateK reciprocalK : K -> K

    one-not-zeroK :
      oneK != zeroK

    add-commutativeK :
      (x y : K) ->
      addK x y == addK y x
    add-associativeK :
      (x y z : K) ->
      addK (addK x y) z == addK x (addK y z)
    add-zeroK :
      (x : K) ->
      addK x zeroK == x
    add-inverseK :
      (x : K) ->
      addK x (negateK x) == zeroK

    multiply-commutativeK :
      (x y : K) ->
      multiplyK x y == multiplyK y x
    multiply-associativeK :
      (x y z : K) ->
      multiplyK (multiplyK x y) z ==
      multiplyK x (multiplyK y z)
    multiply-oneK :
      (x : K) ->
      multiplyK x oneK == x
    multiply-zeroK :
      (x : K) ->
      multiplyK x zeroK == zeroK
    distributeK :
      (x y z : K) ->
      multiplyK x (addK y z) ==
      addK (multiplyK x y) (multiplyK x z)
    reciprocal-zeroK :
      reciprocalK zeroK == zeroK
    multiply-reciprocalK :
      (x : K) ->
      x != zeroK ->
      multiplyK x (reciprocalK x) == oneK

open Field

record NormedField
  {r k : Level}
  (R : Set r)
  (reals : CompleteOrderedField R)
  (K : Set k) :
  Set (lsuc (r ⊔ k)) where

  field
    fieldStructure : Field K
    normK : K -> R

    norm-nonnegativeK :
      (x : K) ->
      lessOrEqualR reals (zeroR reals) (normK x)
    norm-zeroK :
      normK (zeroK fieldStructure) == zeroR reals
    norm-zero-onlyK :
      (x : K) ->
      normK x == zeroR reals ->
      x == zeroK fieldStructure
    norm-oneK :
      normK (oneK fieldStructure) == oneR reals
    norm-negateK :
      (x : K) ->
      normK (negateK fieldStructure x) == normK x
    norm-addK :
      (x y : K) ->
      lessOrEqualR reals
        (normK (addK fieldStructure x y))
        (addR reals (normK x) (normK y))
    norm-multiplyK :
      (x y : K) ->
      normK (multiplyK fieldStructure x y) ==
      multiplyR reals (normK x) (normK y)

open NormedField

Matrix :
  {i k : Level} ->
  Set i ->
  Set k ->
  Set (i ⊔ k)
Matrix I K =
  I -> I -> K

Vector :
  {i k : Level} ->
  Set i ->
  Set k ->
  Set (i ⊔ k)
Vector I K =
  I -> K

VectorEqual :
  {i k : Level} ->
  {I : Set i} ->
  {K : Set k} ->
  Vector I K ->
  Vector I K ->
  Set (i ⊔ k)
VectorEqual {I = I} v w =
  (index : I) ->
  v index == w index

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
  {k : Level} ->
  {K : Set k} ->
  Field K ->
  {n : Nat} ->
  (Fin n -> K) ->
  K
sumFin fieldData {zero} term =
  zeroK fieldData
sumFin fieldData {suc n} term =
  addK fieldData
    (term fzero)
    (sumFin fieldData (λ j -> term (fsuc j)))

sumIndex :
  {i k : Level} ->
  {I : Set i} ->
  {K : Set k} ->
  FiniteIndex I ->
  Field K ->
  (I -> K) ->
  K
sumIndex finite fieldData term =
  sumFin fieldData (λ j -> term (fromFin finite j))

sumFinR :
  {r : Level} ->
  {R : Set r} ->
  CompleteOrderedField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFinR reals {zero} term =
  zeroR reals
sumFinR reals {suc n} term =
  addR reals
    (term fzero)
    (sumFinR reals (λ j -> term (fsuc j)))

subtractK :
  {r k : Level} ->
  {R : Set r} ->
  {K : Set k} ->
  {reals : CompleteOrderedField R} ->
  NormedField R reals K ->
  K ->
  K ->
  K
subtractK scalars x y =
  addK (fieldStructure scalars)
    x
    (negateK (fieldStructure scalars) y)

matrixVectorProduct :
  {r i k : Level} ->
  {R : Set r} ->
  {I : Set i} ->
  {K : Set k} ->
  {reals : CompleteOrderedField R} ->
  FiniteIndex I ->
  (scalars : NormedField R reals K) ->
  Matrix I K ->
  Vector I K ->
  Vector I K
matrixVectorProduct finite scalars A v row =
  sumIndex finite (fieldStructure scalars)
    (λ column ->
      multiplyK (fieldStructure scalars)
        (A row column)
        (v column))

scalarVector :
  {r i k : Level} ->
  {R : Set r} ->
  {I : Set i} ->
  {K : Set k} ->
  {reals : CompleteOrderedField R} ->
  NormedField R reals K ->
  K ->
  Vector I K ->
  Vector I K
scalarVector scalars scalar v index =
  multiplyK (fieldStructure scalars) scalar (v index)

NonzeroVector :
  {r i k : Level} ->
  {R : Set r} ->
  {I : Set i} ->
  {K : Set k} ->
  {reals : CompleteOrderedField R} ->
  NormedField R reals K ->
  Vector I K ->
  Set (i ⊔ k)
NonzeroVector {I = I} scalars v =
  Exists I
    (λ index ->
      v index != zeroK (fieldStructure scalars))

HasEigenvalue :
  {r i k : Level} ->
  {R : Set r} ->
  {I : Set i} ->
  {K : Set k} ->
  {reals : CompleteOrderedField R} ->
  FiniteIndex I ->
  NormedField R reals K ->
  Matrix I K ->
  K ->
  Set (i ⊔ k)
HasEigenvalue {I = I} {K = K} finite scalars A eigenvalue =
  Exists (Vector I K)
    (λ eigenvector ->
      Both
        (NonzeroVector scalars eigenvector)
        (VectorEqual
          (matrixVectorProduct finite scalars A eigenvector)
          (scalarVector scalars eigenvalue eigenvector)))

sumRowNormsExcept :
  {r i k : Level} ->
  {R : Set r} ->
  {I : Set i} ->
  {K : Set k} ->
  FiniteIndex I ->
  (reals : CompleteOrderedField R) ->
  {scalars : NormedField R reals K} ->
  Matrix I K ->
  I ->
  R
sumRowNormsExcept finite reals {scalars} A row =
  sumFinR reals
    (λ column ->
      select
        (equalIndex finite row (fromFin finite column))
        (zeroR reals)
        (normK scalars (A row (fromFin finite column))))

GershgorinConclusion :
  {r i k : Level} ->
  {R : Set r} ->
  {I : Set i} ->
  {K : Set k} ->
  FiniteIndex I ->
  (reals : CompleteOrderedField R) ->
  (scalars : NormedField R reals K) ->
  Matrix I K ->
  K ->
  Set (r ⊔ i)
GershgorinConclusion {I = I} finite reals scalars A eigenvalue =
  Exists I
    (λ row ->
      lessOrEqualR reals
        (normK scalars
          (subtractK scalars eigenvalue (A row row)))
        (sumRowNormsExcept finite reals {scalars} A row))

gershgorin-circle-theorem : Setω
gershgorin-circle-theorem =
  {r i k : Level} ->
  (R : Set r) ->
  (reals : CompleteOrderedField R) ->
  (I : Set i) ->
  (finite : FiniteIndex I) ->
  (K : Set k) ->
  (scalars : NormedField R reals K) ->
  (A : Matrix I K) ->
  (eigenvalue : K) ->
  HasEigenvalue finite scalars A eigenvalue ->
  GershgorinConclusion finite reals scalars A eigenvalue
