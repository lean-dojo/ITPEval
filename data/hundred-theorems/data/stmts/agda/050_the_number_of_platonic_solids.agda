-- Statement-only formalization of "The Number of Platonic Solids" from Hundred Theorems
-- artifact hundred-theorems__agda__050: a full-dimensional polytope in real three-space has
-- constant facet-edge and vertex-edge counts exactly for the five Platonic pairs. This file
-- contains no proof.

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; _⊔_)

infix 4 _!=_

data Bottom : Set where

Not : {a : Level} -> Set a -> Set a
Not A = A -> Bottom

_!=_ : {a : Level} -> {A : Set a} -> A -> A -> Set a
x != y = Not (x == y)

record Both {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor both
  field
    first  : A
    second : B

data Either {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  left  : A -> Either A B
  right : B -> Either A B

record Iff {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists {a p : Level} (A : Set a) (P : A -> Set p) :
    Set (a ⊔ p) where
  constructor witness
  field
    value    : A
    property : P value

record CompleteOrderedField (R : Set) : Set1 where
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
      Either (lessOrEqual x y) (lessOrEqual y x)
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
      Both (lessOrEqual zeroR oneR) (zeroR != oneR)

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
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqual x upper) ->
              lessOrEqual supremum upper))

open CompleteOrderedField

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Vector : Set -> Nat -> Set
Vector R n =
  Fin n -> R

Region : Set -> Nat -> Set1
Region R n =
  Vector R n -> Set

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqual reals x y) (x != y)

zeroVector :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n
zeroVector reals i =
  zeroR reals

VectorEqual :
  {R : Set} ->
  {n : Nat} ->
  Vector R n ->
  Vector R n ->
  Set
VectorEqual {n = n} x y =
  (i : Fin n) -> x i == y i

Subset :
  {R : Set} ->
  {n : Nat} ->
  Region R n ->
  Region R n ->
  Set
Subset {R} {n} smaller larger =
  (x : Vector R n) ->
  smaller x ->
  larger x

RegionEquivalent :
  {R : Set} ->
  {n : Nat} ->
  Region R n ->
  Region R n ->
  Set
RegionEquivalent {R} {n} firstRegion secondRegion =
  (x : Vector R n) ->
  Iff (firstRegion x) (secondRegion x)

sumFin :
  {R : Set} ->
  CompleteOrderedField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {n = zero} values =
  zeroR reals
sumFin reals {n = suc n} values =
  add reals
    (values fzero)
    (sumFin reals (\ i -> values (fsuc i)))

weightedSum :
  {R : Set} ->
  {dimension count : Nat} ->
  CompleteOrderedField R ->
  (Fin count -> Vector R dimension) ->
  (Fin count -> R) ->
  Vector R dimension
weightedSum reals points coefficients coordinate =
  sumFin reals
    (\ i ->
      multiply reals
        (coefficients i)
        (points i coordinate))

linearCombination :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  R ->
  Vector R n ->
  Vector R n ->
  Vector R n
linearCombination reals t x y coordinate =
  add reals
    (multiply reals t (x coordinate))
    (multiply reals
      (subtract reals (oneR reals) t)
      (y coordinate))

Convex :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Region R n ->
  Set
Convex {R} {n} reals body =
  (x y : Vector R n) ->
  body x ->
  body y ->
  (t : R) ->
  lessOrEqual reals (zeroR reals) t ->
  lessOrEqual reals t (oneR reals) ->
  body (linearCombination reals t x y)

ConvexHull :
  {R : Set} ->
  {dimension count : Nat} ->
  CompleteOrderedField R ->
  (Fin count -> Vector R dimension) ->
  Region R dimension
ConvexHull {R} {count = count} reals points x =
  Exists (Fin count -> R)
    (\ coefficients ->
      Both
        ((i : Fin count) ->
          lessOrEqual reals (zeroR reals) (coefficients i))
        (Both
          (sumFin reals coefficients == oneR reals)
          (VectorEqual
            (weightedSum reals points coefficients)
            x)))

Polytope :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R 3 ->
  Set
Polytope {R} reals body =
  Exists Nat
    (\ count ->
      Exists (Fin count -> Vector R 3)
        (\ points ->
          RegionEquivalent body (ConvexHull reals points)))

FaceOf :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R 3 ->
  Region R 3 ->
  Set
FaceOf {R} reals face body =
  Both
    (Subset face body)
    (Both
      (Convex reals face)
      ((x y : Vector R 3) ->
        body x ->
        body y ->
        (t : R) ->
        StrictLess reals (zeroR reals) t ->
        StrictLess reals t (oneR reals) ->
        face (linearCombination reals t x y) ->
        Both (face x) (face y)))

AffineIndependent :
  {R : Set} ->
  {count : Nat} ->
  CompleteOrderedField R ->
  (Fin count -> Vector R 3) ->
  Set
AffineIndependent {R} {count = count} reals points =
  (coefficients : Fin count -> R) ->
  sumFin reals coefficients == zeroR reals ->
  VectorEqual
    (weightedSum reals points coefficients)
    (zeroVector reals) ->
  (i : Fin count) ->
  coefficients i == zeroR reals

PointsIn :
  {R : Set} ->
  {count : Nat} ->
  Region R 3 ->
  (Fin count -> Vector R 3) ->
  Set
PointsIn {count = count} body points =
  (i : Fin count) ->
  body (points i)

HasAffineDimension :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  Region R 3 ->
  Set
HasAffineDimension {R} reals dimension body =
  Both
    (Exists (Fin (suc dimension) -> Vector R 3)
      (\ points ->
        Both
          (PointsIn body points)
          (AffineIndependent reals points)))
    ((points : Fin (suc (suc dimension)) -> Vector R 3) ->
      PointsIn body points ->
      Not (AffineIndependent reals points))

record HasRegionCardinality
  {R : Set}
  (P : Region R 3 -> Set)
  (cardinality : Nat) : Set1 where
  field
    enumerate :
      Fin cardinality ->
      Region R 3

    enumeration-sound :
      (i : Fin cardinality) ->
      P (enumerate i)

    enumeration-complete :
      (region : Region R 3) ->
      P region ->
      Exists (Fin cardinality)
        (\ i ->
          RegionEquivalent (enumerate i) region)

    enumeration-injective :
      (i j : Fin cardinality) ->
      RegionEquivalent (enumerate i) (enumerate j) ->
      i == j

EdgeOf :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R 3 ->
  Region R 3 ->
  Set
EdgeOf reals polytope edge =
  Both
    (FaceOf reals edge polytope)
    (HasAffineDimension reals 1 edge)

FacetEdgeCount :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R 3 ->
  Nat ->
  Set1
FacetEdgeCount {R} reals polytope count =
  (facet : Region R 3) ->
  Both
    (FaceOf reals facet polytope)
    (HasAffineDimension reals 2 facet) ->
  HasRegionCardinality
    (\ edge ->
      Both
        (EdgeOf reals polytope edge)
        (Subset edge facet))
    count

VertexEdgeCount :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R 3 ->
  Nat ->
  Set1
VertexEdgeCount {R} reals polytope count =
  (vertex : Region R 3) ->
  Both
    (FaceOf reals vertex polytope)
    (HasAffineDimension reals 0 vertex) ->
  HasRegionCardinality
    (\ edge ->
      Both
        (EdgeOf reals polytope edge)
        (Subset vertex edge))
    count

AdmissiblePolytope :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  Nat ->
  Region R 3 ->
  Set1
AdmissiblePolytope reals facetCount vertexCount polytope =
  Both
    (Polytope reals polytope)
    (Both
      (HasAffineDimension reals 3 polytope)
      (Both
        (FacetEdgeCount reals polytope facetCount)
        (VertexEdgeCount reals polytope vertexCount)))

PlatonicCounts :
  Nat ->
  Nat ->
  Set
PlatonicCounts facetCount vertexCount =
  Either
    (Both (facetCount == 3) (vertexCount == 3))
    (Either
      (Both (facetCount == 4) (vertexCount == 3))
      (Either
        (Both (facetCount == 3) (vertexCount == 4))
        (Either
          (Both (facetCount == 5) (vertexCount == 3))
          (Both (facetCount == 3) (vertexCount == 5)))))

the-number-of-platonic-solids : Set1
the-number-of-platonic-solids =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (facetCount vertexCount : Nat) ->
  Iff
    (Exists (Region R 3)
      (AdmissiblePolytope reals facetCount vertexCount))
    (PlatonicCounts facetCount vertexCount)
