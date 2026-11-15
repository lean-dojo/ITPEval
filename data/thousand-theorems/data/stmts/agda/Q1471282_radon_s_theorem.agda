-- Statement-only formalization of thousand-theorems corpus artifact Q1471282,
-- "Radon's theorem": every affine-dependent family over a linear ordered field
-- has a subset whose image and complementary image have intersecting convex
-- hulls. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1471282_radon_s_theorem where

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
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

record LinearOrderedField
  {k : Level}
  (K : Set k) :
  Set (lsuc k) where

  field
    zeroK oneK : K
    addK multiplyK : K -> K -> K
    negateK inverseK : K -> K
    lessOrEqualK : K -> K -> Set k

    one-not-zero :
      oneK != zeroK

    add-commutative :
      (x y : K) ->
      addK x y == addK y x
    add-associative :
      (x y z : K) ->
      addK (addK x y) z == addK x (addK y z)
    add-zero :
      (x : K) ->
      addK x zeroK == x
    add-inverse :
      (x : K) ->
      addK x (negateK x) == zeroK

    multiply-commutative :
      (x y : K) ->
      multiplyK x y == multiplyK y x
    multiply-associative :
      (x y z : K) ->
      multiplyK (multiplyK x y) z ==
      multiplyK x (multiplyK y z)
    multiply-one :
      (x : K) ->
      multiplyK x oneK == x
    distribute :
      (x y z : K) ->
      multiplyK x (addK y z) ==
      addK (multiplyK x y) (multiplyK x z)
    multiply-inverse :
      (x : K) ->
      x != zeroK ->
      multiplyK x (inverseK x) == oneK

    order-reflexive :
      (x : K) ->
      lessOrEqualK x x
    order-transitive :
      (x y z : K) ->
      lessOrEqualK x y ->
      lessOrEqualK y z ->
      lessOrEqualK x z
    order-antisymmetric :
      (x y : K) ->
      lessOrEqualK x y ->
      lessOrEqualK y x ->
      x == y
    order-total :
      (x y : K) ->
      lessOrEqualK x y or lessOrEqualK y x
    add-order :
      (x y z : K) ->
      lessOrEqualK x y ->
      lessOrEqualK (addK z x) (addK z y)
    multiply-nonnegative :
      (x y : K) ->
      lessOrEqualK zeroK x ->
      lessOrEqualK zeroK y ->
      lessOrEqualK zeroK (multiplyK x y)
    zero-less-than-one :
      lessOrEqualK zeroK oneK and zeroK != oneK

open LinearOrderedField

record VectorSpace
  {k e : Level}
  {K : Set k}
  (orderedField : LinearOrderedField K)
  (E : Set e) :
  Set (lsuc (k ⊔ e)) where

  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : K -> E -> E

    add-commutativeE :
      (x y : E) ->
      addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) ->
      addE x zeroE == x
    add-inverseE :
      (x : E) ->
      addE x (negateE x) == zeroE

    scale-one :
      (x : E) ->
      scaleE (oneK orderedField) x == x
    scale-associative :
      (a b : K) ->
      (x : E) ->
      scaleE (multiplyK orderedField a b) x ==
      scaleE a (scaleE b x)
    scale-add-vectors :
      (a : K) ->
      (x y : E) ->
      scaleE a (addE x y) ==
      addE (scaleE a x) (scaleE a y)
    scale-add-scalars :
      (a b : K) ->
      (x : E) ->
      scaleE (addK orderedField a b) x ==
      addE (scaleE a x) (scaleE b x)

open VectorSpace

sumScalars :
  {k : Level}
  {K : Set k} ->
  LinearOrderedField K ->
  {n : Nat} ->
  (Fin n -> K) ->
  K
sumScalars orderedField {zero} terms =
  zeroK orderedField
sumScalars orderedField {suc n} terms =
  addK orderedField
    (terms fzero)
    (sumScalars orderedField (\ j -> terms (fsuc j)))

sumWeighted :
  {i k e : Level}
  {I : Set i}
  {K : Set k}
  {E : Set e}
  {orderedField : LinearOrderedField K} ->
  VectorSpace orderedField E ->
  {n : Nat} ->
  (Fin n -> I) ->
  (Fin n -> K) ->
  (I -> E) ->
  E
sumWeighted space {zero} indices weights f =
  zeroE space
sumWeighted space {suc n} indices weights f =
  addE space
    (scaleE space (weights fzero) (f (indices fzero)))
    (sumWeighted space
      (\ j -> indices (fsuc j))
      (\ j -> weights (fsuc j))
      f)

Injective :
  {i : Level}
  {I : Set i}
  {n : Nat} ->
  (Fin n -> I) ->
  Set i
Injective indices =
  (j l : _) ->
  indices j == indices l ->
  j == l

AffineIndependent :
  {i k e : Level}
  {I : Set i}
  {K : Set k}
  {E : Set e} ->
  (orderedField : LinearOrderedField K) ->
  VectorSpace orderedField E ->
  (I -> E) ->
  Set (i ⊔ k ⊔ e)
AffineIndependent {K = K} orderedField space f =
  {n : Nat} ->
  (indices : Fin n -> _) ->
  Injective indices ->
  (weights : Fin n -> K) ->
  sumScalars orderedField weights == zeroK orderedField ->
  sumWeighted space indices weights f == zeroE space ->
  (j : Fin n) ->
  weights j == zeroK orderedField

ConvexHullOfImage :
  {i k e : Level}
  {I : Set i}
  {K : Set k}
  {E : Set e} ->
  (orderedField : LinearOrderedField K) ->
  VectorSpace orderedField E ->
  (I -> E) ->
  (I -> Set i) ->
  E ->
  Set (i ⊔ k ⊔ e)
ConvexHullOfImage {I = I} {K = K}
    orderedField space f subset point =
  Exists Nat
    (\ n ->
      Exists (Fin (suc n) -> I)
        (\ indices ->
          Exists (Fin (suc n) -> K)
            (\ weights ->
              ((j : Fin (suc n)) -> subset (indices j))
              and
              (((j : Fin (suc n)) ->
                  lessOrEqualK orderedField
                    (zeroK orderedField)
                    (weights j))
                and
                ((sumScalars orderedField weights ==
                    oneK orderedField)
                  and
                  (sumWeighted space indices weights f ==
                    point))))))

radon-s-theorem : Setω
radon-s-theorem =
  {i k e : Level} ->
  (I : Set i) ->
  (K : Set k) ->
  (orderedField : LinearOrderedField K) ->
  (E : Set e) ->
  (space : VectorSpace orderedField E) ->
  (f : I -> E) ->
  Not (AffineIndependent orderedField space f) ->
  Exists (I -> Set i)
    (\ subset ->
      Exists E
        (\ point ->
          ConvexHullOfImage
            orderedField space f subset point
          and
          ConvexHullOfImage
            orderedField space f
            (\ index -> Not (subset index))
            point))
