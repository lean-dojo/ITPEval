-- Statement-only formalization of thousand-theorems corpus artifact Q338886,
-- "Divergence theorem": the Bochner-integral divergence identity on a real
-- rectangular box, allowing a countable exceptional set for differentiability.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q338886_divergence_theorem where

open import Support.Bochner
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open CompleteOrderedField
open NormedVectorSpace
open SigmaAlgebra
open ExtendedNonnegativeReals
open Measure
open BochnerIntegration

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) : Set1 where
  field
    forwardR :
      R -> S
    backwardR :
      S -> R
    forward-after-backwardR :
      (y : S) -> forwardR (backwardR y) == y
    backward-after-forwardR :
      (x : R) -> backwardR (forwardR x) == x
    forward-zeroR :
      forwardR (zeroR source) == zeroR target
    forward-oneR :
      forwardR (oneR source) == oneR target
    forward-addR :
      (x y : R) ->
      forwardR (addR source x y) ==
      addR target (forwardR x) (forwardR y)
    forward-multiplyR :
      (x y : R) ->
      forwardR (multiplyR source x y) ==
      multiplyR target (forwardR x) (forwardR y)
    forward-negateR :
      (x : R) ->
      forwardR (negateR source x) ==
      negateR target (forwardR x)
    forward-reciprocalR :
      (x : R) ->
      forwardR (reciprocalR source x) ==
      reciprocalR target (forwardR x)
    forward-absoluteR :
      (x : R) ->
      forwardR (absoluteR source x) ==
      absoluteR target (forwardR x)
    forward-fromNatR :
      (n : Nat) ->
      forwardR (fromNatR source n) == fromNatR target n
    forward-orderR :
      (x y : R) ->
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) : Set2 where
  field
    equivalent-complete-ordered-field :
      (S : Set) ->
      (other : CompleteOrderedField S) ->
      CompleteOrderedFieldEquivalence reals other

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Vector :
  {a : Level} ->
  Set a ->
  Nat ->
  Set a
Vector R n =
  Fin n -> R

maxR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
maxR reals x y with order-total reals x y
... | left _  = y
... | right _ = x

positivePart :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
positivePart reals x with order-total reals (zeroR reals) x
... | left _  = x
... | right _ = zeroR reals

vectorAddR :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Vector R n
vectorAddR reals x y i =
  addR reals (x i) (y i)

vectorSubtractR :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Vector R n
vectorSubtractR reals x y i =
  subtractR reals (x i) (y i)

vectorScaleR :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  R ->
  Vector R n ->
  Vector R n
vectorScaleR reals scalar x i =
  multiplyR reals scalar (x i)

vectorNormR :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  R
vectorNormR {n = zero} reals x =
  zeroR reals
vectorNormR {n = suc n} reals x =
  maxR reals
    (absoluteR reals (x fzero))
    (vectorNormR reals (\ i -> x (fsuc i)))

vectorDistanceR :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  R
vectorDistanceR reals x y =
  vectorNormR reals (vectorSubtractR reals x y)

vectorSubtractE :
  {e : Level} ->
  {R : Set} ->
  {E : Set e} ->
  {n : Nat} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  Vector E n ->
  Vector E n ->
  Vector E n
vectorSubtractE space x y i =
  subtractE space (x i) (y i)

vectorNormE :
  {e : Level} ->
  {R : Set} ->
  {E : Set e} ->
  {n : Nat} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  Vector E n ->
  R
vectorNormE {n = zero} {reals = reals} space x =
  zeroR reals
vectorNormE {n = suc n} {reals = reals} space x =
  maxR reals
    (normE space (x fzero))
    (vectorNormE space (\ i -> x (fsuc i)))

vectorDistanceE :
  {e : Level} ->
  {R : Set} ->
  {E : Set e} ->
  {n : Nat} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  Vector E n ->
  Vector E n ->
  R
vectorDistanceE space x y =
  vectorNormE space (vectorSubtractE space x y)

PointwiseLessOrEqual :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Set
PointwiseLessOrEqual reals lower upper =
  (i : _) -> lessOrEqualR reals (lower i) (upper i)

ClosedBox :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Predicate (Vector R n)
ClosedBox reals lower upper x =
  (i : _) ->
  Both
    (lessOrEqualR reals (lower i) (x i))
    (lessOrEqualR reals (x i) (upper i))

OpenBox :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Predicate (Vector R n)
OpenBox reals lower upper x =
  (i : _) ->
  Both
    (StrictLess reals (lower i) (x i))
    (StrictLess reals (x i) (upper i))

NormOpen :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Predicate (Vector R n) ->
  Set
NormOpen {R = R} {n = n} reals U =
  (x : Vector R n) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : Vector R n) ->
          StrictLess reals (vectorDistanceR reals y x) radius ->
          U y))

data BorelGenerated
  {R : Set}
  {n : Nat}
  (reals : CompleteOrderedField R) :
  Predicate (Vector R n) -> Set1 where
  borel-open :
    {U : Predicate (Vector R n)} ->
    NormOpen reals U ->
    BorelGenerated reals U
  borel-empty :
    BorelGenerated reals emptySet
  borel-complement :
    {S : Predicate (Vector R n)} ->
    BorelGenerated reals S ->
    BorelGenerated reals (complement S)
  borel-countable-union :
    (sets : Nat -> Predicate (Vector R n)) ->
    ((k : Nat) -> BorelGenerated reals (sets k)) ->
    BorelGenerated reals (countableUnion sets)
  borel-congruent :
    {S T : Predicate (Vector R n)} ->
    ((x : Vector R n) -> Iff (S x) (T x)) ->
    BorelGenerated reals S ->
    BorelGenerated reals T

productFin :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  R
productFin {n = zero} reals terms =
  oneR reals
productFin {n = suc n} reals terms =
  multiplyR reals
    (terms fzero)
    (productFin reals (\ i -> terms (fsuc i)))

boxVolume :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  R
boxVolume reals lower upper =
  productFin reals
    (\ i ->
      positivePart reals
        (subtractR reals (upper i) (lower i)))

record LebesgueSpace
  {R M : Set}
  (reals : CompleteOrderedField R)
  (extended : ExtendedNonnegativeReals R M reals)
  (n : Nat) : Set2 where
  field
    events :
      SigmaAlgebra (Vector R n)
    volume :
      Measure extended events
    measurable-is-borel :
      (S : Predicate (Vector R n)) ->
      measurable events S ->
      BorelGenerated reals S
    borel-is-measurable :
      (S : Predicate (Vector R n)) ->
      BorelGenerated reals S ->
      measurable events S
    closed-box-measurable :
      (lower upper : Vector R n) ->
      measurable events (ClosedBox reals lower upper)
    closed-box-volume :
      (lower upper : Vector R n) ->
      PointwiseLessOrEqual reals lower upper ->
      Exists
        (lessOrEqualR reals
          (zeroR reals)
          (boxVolume reals lower upper))
        (\ nonnegative-volume ->
          outerMass volume (ClosedBox reals lower upper) ==
          finiteM extended
            (boxVolume reals lower upper)
            nonnegative-volume)

open LebesgueSpace

record LebesgueSpaceEquivalence
  {R M : Set}
  (reals : CompleteOrderedField R)
  (extended : ExtendedNonnegativeReals R M reals)
  {n : Nat}
  (left right : LebesgueSpace reals extended n) : Set2 where
  field
    measurable-forward :
      (S : Predicate (Vector R n)) ->
      measurable (events left) S ->
      measurable (events right) S
    measurable-backward :
      (S : Predicate (Vector R n)) ->
      measurable (events right) S ->
      measurable (events left) S
    volume-forward :
      (S : Predicate (Vector R n)) ->
      measurable (events left) S ->
      outerMass (volume left) S == outerMass (volume right) S
    volume-backward :
      (S : Predicate (Vector R n)) ->
      measurable (events right) S ->
      outerMass (volume right) S == outerMass (volume left) S

record MeasureRestriction
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals) : Set2 where
  field
    restrict :
      (measure : Measure extended events) ->
      (S : Predicate A) ->
      measurable events S ->
      Measure extended events
    restricted-mass :
      (measure : Measure extended events) ->
      (S : Predicate A) ->
      (S-measurable : measurable events S) ->
      (T : Predicate A) ->
      outerMass (restrict measure S S-measurable) T ==
      outerMass measure (intersection T S)

open MeasureRestriction

record BochnerIntegralOperator
  {e : Level}
  {A R M : Set}
  {E : Set e}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals) : Set (lsuc e) where
  field
    integration :
      (measure : Measure extended events) ->
      BochnerIntegration reals space events extended measure

open BochnerIntegralOperator

record BochnerIntegralOperatorEquivalence
  {e : Level}
  {A R M : Set}
  {E : Set e}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals)
  (left right :
    BochnerIntegralOperator reals space events extended) :
  Set (lsuc e) where
  field
    lower-integral-forward :
      (measure : Measure extended events) ->
      (g : A -> R) ->
      ((x : A) -> lessOrEqualR reals (zeroR reals) (g x)) ->
      lowerIntegral (integration left measure) g ==
      lowerIntegral (integration right measure) g
    lower-integral-backward :
      (measure : Measure extended events) ->
      (g : A -> R) ->
      ((x : A) -> lessOrEqualR reals (zeroR reals) (g x)) ->
      lowerIntegral (integration right measure) g ==
      lowerIntegral (integration left measure) g
    vector-integral-forward :
      (measure : Measure extended events) ->
      (g : A -> E) ->
      integralVector (integration left measure) g ==
      integralVector (integration right measure) g
    vector-integral-backward :
      (measure : Measure extended events) ->
      (g : A -> E) ->
      integralVector (integration right measure) g ==
      integralVector (integration left measure) g

SetIntegrable :
  {e : Level} ->
  {A R M : Set} ->
  {E : Set e} ->
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  (events : SigmaAlgebra A) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  MeasureRestriction events extended ->
  BochnerIntegralOperator reals space events extended ->
  (measure : Measure extended events) ->
  (S : Predicate A) ->
  measurable events S ->
  (A -> E) ->
  Set (lsuc e)
SetIntegrable {reals = reals} space events extended restrictions
  integrals measure S S-measurable f =
  VectorIntegrable
    reals space events extended
    (restrict restrictions measure S S-measurable)
    (lowerIntegral
      (integration integrals
        (restrict restrictions measure S S-measurable)))
    f

setIntegral :
  {e : Level} ->
  {A R M : Set} ->
  {E : Set e} ->
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  (events : SigmaAlgebra A) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  MeasureRestriction events extended ->
  BochnerIntegralOperator reals space events extended ->
  (measure : Measure extended events) ->
  (S : Predicate A) ->
  measurable events S ->
  (A -> E) ->
  E
setIntegral space events extended restrictions integrals
  measure S S-measurable f =
  integralVector
    (integration integrals
      (restrict restrictions measure S S-measurable))
    f

sumFinE :
  {e : Level} ->
  {E : Set e} ->
  {R : Set} ->
  {n : Nat} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  (Fin n -> E) ->
  E
sumFinE {n = zero} space terms =
  zeroE space
sumFinE {n = suc n} space terms =
  addE space
    (terms fzero)
    (sumFinE space (\ i -> terms (fsuc i)))

basisEntry :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Fin n ->
  Fin n ->
  R
basisEntry {n = zero} reals ()
basisEntry {n = suc n} reals fzero fzero =
  oneR reals
basisEntry {n = suc n} reals fzero (fsuc j) =
  zeroR reals
basisEntry {n = suc n} reals (fsuc i) fzero =
  zeroR reals
basisEntry {n = suc n} reals (fsuc i) (fsuc j) =
  basisEntry reals i j

basisVector :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Fin (suc n) ->
  Vector R (suc n)
basisVector reals i j =
  basisEntry reals i j

skipCoordinate :
  {n : Nat} ->
  Fin (suc n) ->
  Fin n ->
  Fin (suc n)
skipCoordinate fzero j =
  fsuc j
skipCoordinate (fsuc i) fzero =
  fzero
skipCoordinate (fsuc i) (fsuc j) =
  fsuc (skipCoordinate i j)

insertCoordinate :
  {R : Set} ->
  {n : Nat} ->
  Fin (suc n) ->
  R ->
  Vector R n ->
  Vector R (suc n)
insertCoordinate {n = zero} fzero value face fzero =
  value
insertCoordinate {n = suc n} fzero value face fzero =
  value
insertCoordinate {n = suc n} fzero value face (fsuc j) =
  face j
insertCoordinate {n = suc n} (fsuc i) value face fzero =
  face fzero
insertCoordinate {n = suc n} (fsuc i) value face (fsuc j) =
  insertCoordinate i value (\ k -> face (fsuc k)) j

faceLower :
  {R : Set} ->
  {n : Nat} ->
  Vector R (suc n) ->
  Fin (suc n) ->
  Vector R n
faceLower lower i j =
  lower (skipCoordinate i j)

faceUpper :
  {R : Set} ->
  {n : Nat} ->
  Vector R (suc n) ->
  Fin (suc n) ->
  Vector R n
faceUpper upper i j =
  upper (skipCoordinate i j)

record ContinuousLinearMap
  {e : Level}
  {R : Set}
  {E : Set e}
  {n : Nat}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals) : Set (lsuc e) where
  field
    linear-map :
      Vector R n -> Vector E n
    map-add :
      (x y : Vector R n) ->
      (i : Fin n) ->
      linear-map (vectorAddR reals x y) i ==
      addE space (linear-map x i) (linear-map y i)
    map-scale :
      (scalar : R) ->
      (x : Vector R n) ->
      (i : Fin n) ->
      linear-map (vectorScaleR reals scalar x) i ==
      scaleE space scalar (linear-map x i)
    operator-bound :
      R
    operator-bound-nonnegative :
      lessOrEqualR reals (zeroR reals) operator-bound
    bounded :
      (x : Vector R n) ->
      lessOrEqualR reals
        (vectorNormE space (linear-map x))
        (multiplyR reals operator-bound (vectorNormR reals x))

open ContinuousLinearMap

ContinuousOn :
  {e : Level} ->
  {R : Set} ->
  {E : Set e} ->
  {n : Nat} ->
  (reals : CompleteOrderedField R) ->
  (space : NormedVectorSpace R E reals) ->
  (Vector R n -> Vector E n) ->
  Predicate (Vector R n) ->
  Set
ContinuousOn {R = R} {n = n} reals space f S =
  (x : Vector R n) ->
  S x ->
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : Vector R n) ->
          S y ->
          StrictLess reals (vectorDistanceR reals y x) radius ->
          StrictLess reals
            (vectorDistanceE space (f y) (f x))
            epsilon))

DerivativeRemainder :
  {e : Level} ->
  {R : Set} ->
  {E : Set e} ->
  {n : Nat} ->
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  (f : Vector R n -> Vector E n) ->
  ContinuousLinearMap reals space ->
  Vector R n ->
  Vector R n ->
  Vector E n
DerivativeRemainder {reals = reals} space f derivative point y i =
  subtractE space
    (subtractE space (f y i) (f point i))
    (linear-map derivative
      (vectorSubtractR reals y point) i)

HasFDerivAt :
  {e : Level} ->
  {R : Set} ->
  {E : Set e} ->
  {n : Nat} ->
  (reals : CompleteOrderedField R) ->
  (space : NormedVectorSpace R E reals) ->
  (f : Vector R n -> Vector E n) ->
  ContinuousLinearMap reals space ->
  Vector R n ->
  Set
HasFDerivAt {R = R} reals space f derivative point =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : _) ->
          StrictLess reals
            (vectorDistanceR reals y point)
            radius ->
          lessOrEqualR reals
            (vectorNormE space
              (DerivativeRemainder space f derivative point y))
            (multiplyR reals epsilon
              (vectorDistanceR reals y point))))

Countable :
  {A : Set} ->
  Predicate A ->
  Set
Countable {A = A} S =
  Exists (Nat -> A)
    (\ enumeration ->
      (x : A) ->
      S x ->
      Exists Nat (\ k -> enumeration k == x))

divergence :
  {e : Level} ->
  {R : Set} ->
  {E : Set e} ->
  {n : Nat} ->
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  (Vector R (suc n) ->
    ContinuousLinearMap {n = suc n} reals space) ->
  Vector R (suc n) ->
  E
divergence {reals = reals} space derivative x =
  sumFinE space
    (\ i ->
      linear-map (derivative x)
        (basisVector reals i) i)

divergence-theorem :
  {e : Level} ->
  Set (lsuc (lsuc lzero) ⊔ lsuc e)
divergence-theorem {e} =
  (n : Nat) ->
  (R M : Set) ->
  (E : Set e) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (space : NormedVectorSpace R E reals) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (full-lebesgue : LebesgueSpace reals extended (suc n)) ->
  ((other : LebesgueSpace reals extended (suc n)) ->
    LebesgueSpaceEquivalence
      reals extended full-lebesgue other) ->
  (face-lebesgue : LebesgueSpace reals extended n) ->
  ((other : LebesgueSpace reals extended n) ->
    LebesgueSpaceEquivalence
      reals extended face-lebesgue other) ->
  (full-restrictions :
    MeasureRestriction
      (events full-lebesgue)
      extended) ->
  (face-restrictions :
    MeasureRestriction
      (events face-lebesgue)
      extended) ->
  (full-integrals :
    BochnerIntegralOperator
      reals space (events full-lebesgue) extended) ->
  ((other :
    BochnerIntegralOperator
      reals space (events full-lebesgue) extended) ->
    BochnerIntegralOperatorEquivalence
      reals space (events full-lebesgue) extended
      full-integrals other) ->
  (face-integrals :
    BochnerIntegralOperator
      reals space (events face-lebesgue) extended) ->
  ((other :
    BochnerIntegralOperator
      reals space (events face-lebesgue) extended) ->
    BochnerIntegralOperatorEquivalence
      reals space (events face-lebesgue) extended
      face-integrals other) ->
  (a b : Vector R (suc n)) ->
  PointwiseLessOrEqual reals a b ->
  (f : Vector R (suc n) -> Vector E (suc n)) ->
  (f' :
    Vector R (suc n) ->
    ContinuousLinearMap {n = suc n} reals space) ->
  (s : Predicate (Vector R (suc n))) ->
  Countable s ->
  ContinuousOn reals space f (ClosedBox reals a b) ->
  ((x : Vector R (suc n)) ->
    Both
      (OpenBox reals a b x)
      (Not (s x)) ->
    HasFDerivAt reals space f (f' x) x) ->
  SetIntegrable
    space
    (events full-lebesgue)
    extended
    full-restrictions
    full-integrals
    (volume full-lebesgue)
    (ClosedBox reals a b)
    (closed-box-measurable full-lebesgue a b)
    (divergence space f') ->
  setIntegral
    space
    (events full-lebesgue)
    extended
    full-restrictions
    full-integrals
    (volume full-lebesgue)
    (ClosedBox reals a b)
    (closed-box-measurable full-lebesgue a b)
    (divergence space f')
  ==
  sumFinE space
    (\ i ->
      subtractE space
        (setIntegral
          space
          (events face-lebesgue)
          extended
          face-restrictions
          face-integrals
          (volume face-lebesgue)
          (ClosedBox reals (faceLower a i) (faceUpper b i))
          (closed-box-measurable
            face-lebesgue
            (faceLower a i)
            (faceUpper b i))
          (\ x -> f (insertCoordinate i (b i) x) i))
        (setIntegral
          space
          (events face-lebesgue)
          extended
          face-restrictions
          face-integrals
          (volume face-lebesgue)
          (ClosedBox reals (faceLower a i) (faceUpper b i))
          (closed-box-measurable
            face-lebesgue
            (faceLower a i)
            (faceUpper b i))
          (\ x -> f (insertCoordinate i (a i) x) i)))
