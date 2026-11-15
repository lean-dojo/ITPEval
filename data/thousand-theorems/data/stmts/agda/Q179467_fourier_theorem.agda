-- Statement-only formalization of thousand-theorems corpus artifact Q179467,
-- "Fourier theorem": Fourier inversion for integrable Banach-valued functions
-- on finite-dimensional real inner-product spaces, at continuity points and
-- globally for continuous functions. This file contains no proof.

{-# OPTIONS --safe #-}

module Q179467_fourier_theorem where

open import Support.Bochner
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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
  Set ->
  Nat ->
  Set
Vector R n =
  Fin n -> R

VectorEqual :
  {R : Set} ->
  {n : Nat} ->
  Vector R n ->
  Vector R n ->
  Set
VectorEqual {n = n} x y =
  (i : Fin n) -> x i == y i

sumVector :
  {R : Set} ->
  CompleteOrderedField R ->
  (n : Nat) ->
  Vector R n ->
  R
sumVector reals zero terms =
  zeroR reals
sumVector reals (suc n) terms =
  addR reals
    (terms fzero)
    (sumVector reals n (\ i -> terms (fsuc i)))

productVector :
  {R : Set} ->
  CompleteOrderedField R ->
  (n : Nat) ->
  Vector R n ->
  R
productVector reals zero terms =
  oneR reals
productVector reals (suc n) terms =
  multiplyR reals
    (terms fzero)
    (productVector reals n (\ i -> terms (fsuc i)))

vectorAdd :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Vector R n
vectorAdd reals x y i =
  addR reals (x i) (y i)

vectorScale :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  R ->
  Vector R n ->
  Vector R n
vectorScale reals scalar x i =
  multiplyR reals scalar (x i)

record RealInnerProductSpace
  (R V : Set)
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R V reals) : Set1 where
  field
    inner :
      V -> V -> R
    inner-add-left :
      (x y z : V) ->
      inner (addE space x y) z ==
      addR reals (inner x z) (inner y z)
    inner-scale-left :
      (a : R) ->
      (x y : V) ->
      inner (scaleE space a x) y ==
      multiplyR reals a (inner x y)
    inner-symmetric :
      (x y : V) ->
      inner x y == inner y x
    inner-nonnegative :
      (x : V) ->
      lessOrEqualR reals (zeroR reals) (inner x x)
    inner-definite :
      (x : V) ->
      inner x x == zeroR reals ->
      x == zeroE space
    norm-square :
      (x : V) ->
      multiplyR reals (normE space x) (normE space x) ==
      inner x x

open RealInnerProductSpace

record FiniteDimensionalInnerProduct
  {R V : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R V reals)
  (innerSpace : RealInnerProductSpace R V reals space) : Set1 where
  field
    dimension :
      Nat
    toCoordinates :
      V -> Vector R dimension
    fromCoordinates :
      Vector R dimension -> V
    coordinates-after-vector :
      (x : Vector R dimension) ->
      VectorEqual (toCoordinates (fromCoordinates x)) x
    vector-after-coordinates :
      (x : V) ->
      fromCoordinates (toCoordinates x) == x
    coordinates-add :
      (x y : V) ->
      VectorEqual
        (toCoordinates (addE space x y))
        (vectorAdd reals (toCoordinates x) (toCoordinates y))
    coordinates-scale :
      (a : R) ->
      (x : V) ->
      VectorEqual
        (toCoordinates (scaleE space a x))
        (vectorScale reals a (toCoordinates x))
    coordinates-orthonormal :
      (x y : V) ->
      inner innerSpace x y ==
      sumVector reals dimension
        (\ i ->
          multiplyR reals
            (toCoordinates x i)
            (toCoordinates y i))

open FiniteDimensionalInnerProduct

NormOpen :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R V reals ->
  Predicate V ->
  Set
NormOpen {R = R} {reals = reals} space U =
  (x : _) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : _) ->
          StrictLess reals (distanceE space y x) radius ->
          U y))

data BorelGenerated
  {R V : Set}
  {reals : CompleteOrderedField R}
  (space : NormedVectorSpace R V reals) :
  Predicate V -> Set1 where
  borel-open :
    {U : Predicate V} ->
    NormOpen space U ->
    BorelGenerated space U
  borel-empty :
    BorelGenerated space emptySet
  borel-complement :
    {S : Predicate V} ->
    BorelGenerated space S ->
    BorelGenerated space (complement S)
  borel-countable-union :
    (sets : Nat -> Predicate V) ->
    ((n : Nat) -> BorelGenerated space (sets n)) ->
    BorelGenerated space (countableUnion sets)
  borel-congruent :
    {S T : Predicate V} ->
    ((x : V) -> Iff (S x) (T x)) ->
    BorelGenerated space S ->
    BorelGenerated space T

record BorelSpace
  {R V : Set}
  {reals : CompleteOrderedField R}
  (space : NormedVectorSpace R V reals)
  (events : SigmaAlgebra V) : Set2 where
  field
    borel-measurable :
      (S : Predicate V) ->
      BorelGenerated space S ->
      measurable events S
    measurable-borel :
      (S : Predicate V) ->
      measurable events S ->
      BorelGenerated space S

CoordinatewiseOrdered :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Set
CoordinatewiseOrdered {n = n} reals lower upper =
  (i : Fin n) ->
  lessOrEqualR reals (lower i) (upper i)

CoordinateBox :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  {space : NormedVectorSpace R V reals} ->
  {innerSpace : RealInnerProductSpace R V reals space} ->
  (finite : FiniteDimensionalInnerProduct reals space innerSpace) ->
  Vector R (dimension finite) ->
  Vector R (dimension finite) ->
  Predicate V
CoordinateBox {reals = reals} finite lower upper x =
  (i : Fin (dimension finite)) ->
  Both
    (lessOrEqualR reals
      (lower i)
      (toCoordinates finite x i))
    (StrictLess reals
      (toCoordinates finite x i)
      (upper i))

coordinateBoxVolume :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  {space : NormedVectorSpace R V reals} ->
  {innerSpace : RealInnerProductSpace R V reals space} ->
  (finite : FiniteDimensionalInnerProduct reals space innerSpace) ->
  Vector R (dimension finite) ->
  Vector R (dimension finite) ->
  R
coordinateBoxVolume {reals = reals} finite lower upper =
  productVector reals (dimension finite)
    (\ i -> subtractR reals (upper i) (lower i))

record EuclideanLebesguePresentation
  (R M V : Set)
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R V reals)
  (innerSpace : RealInnerProductSpace R V reals space)
  (finite : FiniteDimensionalInnerProduct reals space innerSpace) : Set2 where
  field
    events :
      SigmaAlgebra V
    extended :
      ExtendedNonnegativeReals R M reals
    volume :
      Measure extended events
    borel-space :
      BorelSpace space events
    coordinate-box-volume-nonnegative :
      (lower upper : Vector R (dimension finite)) ->
      CoordinatewiseOrdered reals lower upper ->
      lessOrEqualR reals
        (zeroR reals)
        (coordinateBoxVolume finite lower upper)
    volume-coordinate-box :
      (lower upper : Vector R (dimension finite)) ->
      (ordered : CoordinatewiseOrdered reals lower upper) ->
      outerMass volume (CoordinateBox finite lower upper) ==
      finiteM extended
        (coordinateBoxVolume finite lower upper)
        (coordinate-box-volume-nonnegative lower upper ordered)

open EuclideanLebesguePresentation

record ComplexNumber (R : Set) : Set where
  constructor complex
  field
    realPart :
      R
    imaginaryPart :
      R

open ComplexNumber

zeroC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R
zeroC reals =
  complex (zeroR reals) (zeroR reals)

oneC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R
oneC reals =
  complex (oneR reals) (zeroR reals)

fromReal :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  ComplexNumber R
fromReal reals x =
  complex x (zeroR reals)

addC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  ComplexNumber R ->
  ComplexNumber R
addC reals (complex a b) (complex c d) =
  complex
    (addR reals a c)
    (addR reals b d)

negateC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  ComplexNumber R
negateC reals (complex a b) =
  complex (negateR reals a) (negateR reals b)

subtractC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  ComplexNumber R ->
  ComplexNumber R
subtractC reals x y =
  addC reals x (negateC reals y)

multiplyC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  ComplexNumber R ->
  ComplexNumber R
multiplyC reals (complex a b) (complex c d) =
  complex
    (addR reals
      (multiplyR reals a c)
      (negateR reals (multiplyR reals b d)))
    (addR reals
      (multiplyR reals a d)
      (multiplyR reals b c))

powerC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  Nat ->
  ComplexNumber R
powerC reals z zero =
  oneC reals
powerC reals z (suc n) =
  multiplyC reals (powerC reals z n) z

factorial :
  Nat ->
  Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

sumFirstC :
  {R : Set} ->
  CompleteOrderedField R ->
  (ComplexNumber R -> ComplexNumber R -> ComplexNumber R) ->
  (Nat -> ComplexNumber R) ->
  Nat ->
  ComplexNumber R
sumFirstC reals add terms zero =
  zeroC reals
sumFirstC reals add terms (suc n) =
  add (sumFirstC reals add terms n) (terms n)

record ComplexModulus
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    modulus :
      ComplexNumber R -> R
    modulus-nonnegative :
      (z : ComplexNumber R) ->
      lessOrEqualR reals (zeroR reals) (modulus z)
    modulus-square :
      (z : ComplexNumber R) ->
      multiplyR reals (modulus z) (modulus z) ==
      addR reals
        (multiplyR reals (realPart z) (realPart z))
        (multiplyR reals (imaginaryPart z) (imaginaryPart z))

open ComplexModulus

distanceC :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  ComplexModulus reals ->
  ComplexNumber R ->
  ComplexNumber R ->
  R
distanceC {reals = reals} complexModulus x y =
  modulus complexModulus (subtractC reals x y)

complexExponentialTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  Nat ->
  ComplexNumber R
complexExponentialTerm reals z n =
  multiplyC reals
    (powerC reals z n)
    (fromReal reals
      (reciprocalR reals
        (fromNatR reals (factorial n))))

ComplexExponentialValue :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  ComplexModulus reals ->
  ComplexNumber R ->
  ComplexNumber R ->
  Set
ComplexExponentialValue reals complexModulus z value =
  SequentialLimit reals (distanceC complexModulus)
    (\ n ->
      sumFirstC reals (addC reals)
        (complexExponentialTerm reals z)
        n)
    value

sumFirstR :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirstR reals terms zero =
  zeroR reals
sumFirstR reals terms (suc n) =
  addR reals (sumFirstR reals terms n) (terms n)

powerR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
powerR reals x zero =
  oneR reals
powerR reals x (suc n) =
  multiplyR reals (powerR reals x n) x

leibnizTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
leibnizTerm reals n =
  multiplyR reals
    (powerR reals (negateR reals (oneR reals)) n)
    (reciprocalR reals
      (fromNatR reals
        (suc ((suc (suc zero)) * n))))

record PiValue
  {R : Set}
  (reals : CompleteOrderedField R)
  (pi : R) : Set where
  field
    pi-positive :
      Positive reals pi
    leibniz-series :
      SequentialLimit reals (distanceR reals)
        (\ n -> sumFirstR reals (leibnizTerm reals) n)
        (multiplyR reals pi
          (reciprocalR reals
            (fromNatR reals
              (suc (suc (suc (suc zero)))))))

record ComplexNormedSpace
  (R E : Set)
  (reals : CompleteOrderedField R)
  (complexModulus : ComplexModulus reals) : Set1 where
  field
    realSpace :
      NormedVectorSpace R E reals
    scaleC :
      ComplexNumber R -> E -> E
    scale-oneC :
      (x : E) ->
      scaleC (oneC reals) x == x
    scale-multiplyC :
      (a b : ComplexNumber R) ->
      (x : E) ->
      scaleC (multiplyC reals a b) x ==
      scaleC a (scaleC b x)
    scale-add-scalarsC :
      (a b : ComplexNumber R) ->
      (x : E) ->
      scaleC (addC reals a b) x ==
      addE realSpace (scaleC a x) (scaleC b x)
    scale-add-vectorsC :
      (a : ComplexNumber R) ->
      (x y : E) ->
      scaleC a (addE realSpace x y) ==
      addE realSpace (scaleC a x) (scaleC a y)
    scale-real :
      (a : R) ->
      (x : E) ->
      scaleC (fromReal reals a) x ==
      scaleE realSpace a x
    norm-scaleC :
      (a : ComplexNumber R) ->
      (x : E) ->
      normE realSpace (scaleC a x) ==
      multiplyR reals
        (modulus complexModulus a)
        (normE realSpace x)

open ComplexNormedSpace

forwardPhase :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  {space : NormedVectorSpace R V reals} ->
  (innerSpace : RealInnerProductSpace R V reals space) ->
  R ->
  V ->
  V ->
  ComplexNumber R
forwardPhase {reals = reals} innerSpace pi frequency point =
  complex
    (zeroR reals)
    (negateR reals
      (multiplyR reals
        (multiplyR reals (fromNatR reals (suc (suc zero))) pi)
        (inner innerSpace frequency point)))

inversePhase :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  {space : NormedVectorSpace R V reals} ->
  (innerSpace : RealInnerProductSpace R V reals space) ->
  R ->
  V ->
  V ->
  ComplexNumber R
inversePhase {reals = reals} innerSpace pi frequency point =
  complex
    (zeroR reals)
    (multiplyR reals
      (multiplyR reals (fromNatR reals (suc (suc zero))) pi)
      (inner innerSpace frequency point))

record FourierKernel
  {R V : Set}
  (reals : CompleteOrderedField R)
  (complexModulus : ComplexModulus reals)
  {space : NormedVectorSpace R V reals}
  (innerSpace : RealInnerProductSpace R V reals space) : Set1 where
  field
    pi :
      R
    pi-value :
      PiValue reals pi
    forwardKernel :
      V -> V -> ComplexNumber R
    inverseKernel :
      V -> V -> ComplexNumber R
    forward-kernel-value :
      (frequency point : V) ->
      ComplexExponentialValue reals complexModulus
        (forwardPhase innerSpace pi frequency point)
        (forwardKernel frequency point)
    inverse-kernel-value :
      (frequency point : V) ->
      ComplexExponentialValue reals complexModulus
        (inversePhase innerSpace pi frequency point)
        (inverseKernel frequency point)

open FourierKernel

fourierTransform :
  {R M V E : Set} ->
  {reals : CompleteOrderedField R} ->
  {complexModulus : ComplexModulus reals} ->
  {domain : NormedVectorSpace R V reals} ->
  {innerSpace : RealInnerProductSpace R V reals domain} ->
  {events : SigmaAlgebra V} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  {measure : Measure extended events} ->
  (codomain : ComplexNormedSpace R E reals complexModulus) ->
  BochnerIntegration reals (realSpace codomain) events extended measure ->
  FourierKernel reals complexModulus innerSpace ->
  (V -> E) ->
  V ->
  E
fourierTransform codomain integration kernel f frequency =
  integralVector integration
    (\ point ->
      scaleC codomain
        (forwardKernel kernel frequency point)
        (f point))

inverseFourierTransform :
  {R M V E : Set} ->
  {reals : CompleteOrderedField R} ->
  {complexModulus : ComplexModulus reals} ->
  {domain : NormedVectorSpace R V reals} ->
  {innerSpace : RealInnerProductSpace R V reals domain} ->
  {events : SigmaAlgebra V} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  {measure : Measure extended events} ->
  (codomain : ComplexNormedSpace R E reals complexModulus) ->
  BochnerIntegration reals (realSpace codomain) events extended measure ->
  FourierKernel reals complexModulus innerSpace ->
  (V -> E) ->
  V ->
  E
inverseFourierTransform codomain integration kernel f point =
  integralVector integration
    (\ frequency ->
      scaleC codomain
        (inverseKernel kernel frequency point)
        (f frequency))

ContinuousAt :
  {R V E : Set} ->
  (reals : CompleteOrderedField R) ->
  (domain : NormedVectorSpace R V reals) ->
  (codomain : NormedVectorSpace R E reals) ->
  (V -> E) ->
  V ->
  Set
ContinuousAt {R = R} {V = V} reals domain codomain f point =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((x : V) ->
          StrictLess reals (distanceE domain x point) delta ->
          StrictLess reals
            (distanceE codomain (f x) (f point))
            epsilon))

Continuous :
  {R V E : Set} ->
  (reals : CompleteOrderedField R) ->
  (domain : NormedVectorSpace R V reals) ->
  (codomain : NormedVectorSpace R E reals) ->
  (V -> E) ->
  Set
Continuous {V = V} reals domain codomain f =
  (point : V) ->
  ContinuousAt reals domain codomain f point

FunctionEqual :
  {A B : Set} ->
  (A -> B) ->
  (A -> B) ->
  Set
FunctionEqual {A = A} f g =
  (x : A) -> f x == g x

record FourierContext
  (R M V E : Set) : Set2 where
  field
    reals :
      CompleteOrderedField R
    real-number-presentation :
      RealNumberPresentation reals
    domain :
      NormedVectorSpace R V reals
    inner-space :
      RealInnerProductSpace R V reals domain
    finite-dimensional :
      FiniteDimensionalInnerProduct reals domain inner-space
    complex-modulus :
      ComplexModulus reals
    codomain :
      ComplexNormedSpace R E reals complex-modulus
    codomain-complete :
      Complete reals (distanceE (realSpace codomain))
    lebesgue :
      EuclideanLebesguePresentation
        R M V reals domain inner-space finite-dimensional
    integration :
      BochnerIntegration reals (realSpace codomain)
        (events lebesgue)
        (extended lebesgue)
        (volume lebesgue)
    kernel :
      FourierKernel reals complex-modulus inner-space

open FourierContext

IntegrableInContext :
  {R M V E : Set} ->
  (context : FourierContext R M V E) ->
  (V -> E) ->
  Set1
IntegrableInContext context f =
  VectorIntegrable
    (reals context)
    (realSpace (codomain context))
    (events (lebesgue context))
    (extended (lebesgue context))
    (volume (lebesgue context))
    (lowerIntegral (integration context))
    f

fourierInContext :
  {R M V E : Set} ->
  (context : FourierContext R M V E) ->
  (V -> E) ->
  V ->
  E
fourierInContext context =
  fourierTransform
    (codomain context)
    (integration context)
    (kernel context)

inverseFourierInContext :
  {R M V E : Set} ->
  (context : FourierContext R M V E) ->
  (V -> E) ->
  V ->
  E
inverseFourierInContext context =
  inverseFourierTransform
    (codomain context)
    (integration context)
    (kernel context)

fourier-inversion-at-continuity-point : Set2
fourier-inversion-at-continuity-point =
  (R M V E : Set) ->
  (context : FourierContext R M V E) ->
  (f : V -> E) ->
  IntegrableInContext context f ->
  IntegrableInContext context (fourierInContext context f) ->
  (point : V) ->
  ContinuousAt
    (reals context)
    (domain context)
    (realSpace (codomain context))
    f point ->
  inverseFourierInContext context
    (fourierInContext context f)
    point ==
  f point

continuous-fourier-inversion : Set2
continuous-fourier-inversion =
  (R M V E : Set) ->
  (context : FourierContext R M V E) ->
  (f : V -> E) ->
  Continuous
    (reals context)
    (domain context)
    (realSpace (codomain context))
    f ->
  IntegrableInContext context f ->
  IntegrableInContext context (fourierInContext context f) ->
  FunctionEqual
    (inverseFourierInContext context
      (fourierInContext context f))
    f
