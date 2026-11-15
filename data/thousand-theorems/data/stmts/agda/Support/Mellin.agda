-- Foundational definitions for the statement-only Mellin inversion encoding.
-- This support module contains no proof.

{-# OPTIONS --safe #-}

module Support.Mellin where

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

OpenInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Predicate R
OpenInterval reals lower upper point =
  Both
    (StrictLess reals lower point)
    (StrictLess reals point upper)

data BorelGenerated
  {R : Set}
  (reals : CompleteOrderedField R) :
  Predicate R -> Set1 where
  borel-open-interval :
    (lower upper : R) ->
    BorelGenerated reals (OpenInterval reals lower upper)
  borel-empty :
    BorelGenerated reals emptySet
  borel-complement :
    {S : Predicate R} ->
    BorelGenerated reals S ->
    BorelGenerated reals (complement S)
  borel-countable-union :
    (sets : Nat -> Predicate R) ->
    ((n : Nat) -> BorelGenerated reals (sets n)) ->
    BorelGenerated reals (countableUnion sets)
  borel-congruent :
    {S T : Predicate R} ->
    ((x : R) -> Iff (S x) (T x)) ->
    BorelGenerated reals S ->
    BorelGenerated reals T

record BorelLebesguePresentation
  (R M : Set)
  (reals : CompleteOrderedField R) : Set2 where
  field
    events :
      SigmaAlgebra R
    extended :
      ExtendedNonnegativeReals R M reals
    volume :
      Measure extended events
    borel-measurable :
      (S : Predicate R) ->
      BorelGenerated reals S ->
      measurable events S
    measurable-borel :
      (S : Predicate R) ->
      measurable events S ->
      BorelGenerated reals S
    volume-open-interval :
      (lower upper : R) ->
      (ordered : lessOrEqualR reals lower upper) ->
      Exists
        (lessOrEqualR reals
          (zeroR reals)
          (subtractR reals upper lower))
        (\ nonnegative-length ->
          outerMass volume (OpenInterval reals lower upper) ==
          finiteM extended
            (subtractR reals upper lower)
            nonnegative-length)

open BorelLebesguePresentation

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

imaginaryUnit :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R
imaginaryUnit reals =
  complex (zeroR reals) (oneR reals)

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
  (Nat -> ComplexNumber R) ->
  Nat ->
  ComplexNumber R
sumFirstC reals terms zero =
  zeroC reals
sumFirstC reals terms (suc n) =
  addC reals (sumFirstC reals terms n) (terms n)

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
      sumFirstC reals
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

record StandardComplexAnalysis
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    complexModulus :
      ComplexModulus reals
    exponential :
      ComplexNumber R -> ComplexNumber R
    exponential-value :
      (z : ComplexNumber R) ->
      ComplexExponentialValue reals complexModulus z (exponential z)

    realExponential :
      R -> R
    real-exponential-value :
      (x : R) ->
      exponential (fromReal reals x) ==
      fromReal reals (realExponential x)
    real-exponential-positive :
      (x : R) ->
      Positive reals (realExponential x)

    logarithm :
      R -> R
    exponential-logarithm :
      (x : R) ->
      Positive reals x ->
      realExponential (logarithm x) == x
    logarithm-exponential :
      (x : R) ->
      logarithm (realExponential x) == x

    pi :
      R
    pi-value :
      PiValue reals pi

open StandardComplexAnalysis

positiveRealPower :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  StandardComplexAnalysis reals ->
  R ->
  ComplexNumber R ->
  ComplexNumber R
positiveRealPower {reals = reals} analysis x exponent =
  exponential analysis
    (multiplyC reals exponent
      (fromReal reals (logarithm analysis x)))

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

positiveHalfLine :
  {R : Set} ->
  CompleteOrderedField R ->
  Predicate R
positiveHalfLine reals x =
  Positive reals x

record MellinContext
  (R M E : Set) : Set2 where
  field
    reals :
      CompleteOrderedField R
    real-number-presentation :
      RealNumberPresentation reals
    lebesgue :
      BorelLebesguePresentation R M reals
    analysis :
      StandardComplexAnalysis reals
    codomain :
      ComplexNormedSpace R E reals (complexModulus analysis)
    codomain-complete :
      Complete reals (distanceE (realSpace codomain))

    positive-volume :
      Measure (extended lebesgue) (events lebesgue)
    positive-volume-restriction :
      (S : Predicate R) ->
      outerMass positive-volume S ==
      outerMass (volume lebesgue)
        (intersection S (positiveHalfLine reals))

    full-integration :
      BochnerIntegration reals (realSpace codomain)
        (events lebesgue)
        (extended lebesgue)
        (volume lebesgue)
    positive-integration :
      BochnerIntegration reals (realSpace codomain)
        (events lebesgue)
        (extended lebesgue)
        positive-volume

open MellinContext

verticalPoint :
  {R M E : Set} ->
  (context : MellinContext R M E) ->
  R ->
  R ->
  ComplexNumber R
verticalPoint context sigma y =
  addC (reals context)
    (fromReal (reals context) sigma)
    (multiplyC (reals context)
      (fromReal (reals context) y)
      (imaginaryUnit (reals context)))

mellinIntegrand :
  {R M E : Set} ->
  (context : MellinContext R M E) ->
  (R -> E) ->
  ComplexNumber R ->
  R ->
  E
mellinIntegrand context f s t =
  scaleC (codomain context)
    (positiveRealPower (analysis context) t
      (subtractC (reals context) s (oneC (reals context))))
    (f t)

mellin :
  {R M E : Set} ->
  (context : MellinContext R M E) ->
  (R -> E) ->
  ComplexNumber R ->
  E
mellin context f s =
  integralVector (positive-integration context)
    (mellinIntegrand context f s)

MellinConvergent :
  {R M E : Set} ->
  (context : MellinContext R M E) ->
  (R -> E) ->
  ComplexNumber R ->
  Set1
MellinConvergent context f s =
  VectorIntegrable
    (reals context)
    (realSpace (codomain context))
    (events (lebesgue context))
    (extended (lebesgue context))
    (positive-volume context)
    (lowerIntegral (positive-integration context))
    (mellinIntegrand context f s)

VerticalIntegrable :
  {R M E : Set} ->
  (context : MellinContext R M E) ->
  (ComplexNumber R -> E) ->
  R ->
  Set1
VerticalIntegrable context f sigma =
  VectorIntegrable
    (reals context)
    (realSpace (codomain context))
    (events (lebesgue context))
    (extended (lebesgue context))
    (volume (lebesgue context))
    (lowerIntegral (full-integration context))
    (\ y -> f (verticalPoint context sigma y))

mellinInverseIntegrand :
  {R M E : Set} ->
  (context : MellinContext R M E) ->
  R ->
  (ComplexNumber R -> E) ->
  R ->
  R ->
  E
mellinInverseIntegrand context sigma f x y =
  scaleC (codomain context)
    (positiveRealPower (analysis context) x
      (negateC (reals context) (verticalPoint context sigma y)))
    (f (verticalPoint context sigma y))

twoPi :
  {R M E : Set} ->
  MellinContext R M E ->
  R
twoPi context =
  multiplyR (reals context)
    (fromNatR (reals context) (suc (suc zero)))
    (pi (analysis context))

mellinInv :
  {R M E : Set} ->
  (context : MellinContext R M E) ->
  R ->
  (ComplexNumber R -> E) ->
  R ->
  E
mellinInv context sigma f x =
  scaleC (codomain context)
    (fromReal (reals context)
      (multiplyR (reals context)
        (oneR (reals context))
        (reciprocalR (reals context) (twoPi context))))
    (integralVector (full-integration context)
      (mellinInverseIntegrand context sigma f x))

ContinuousAt :
  {R M E : Set} ->
  (context : MellinContext R M E) ->
  (R -> E) ->
  R ->
  Set
ContinuousAt context f point =
  (epsilon : _) ->
  Positive (reals context) epsilon ->
  Exists _
    (\ delta ->
      Both
        (Positive (reals context) delta)
        ((x : _) ->
          StrictLess (reals context)
            (distanceR (reals context) x point)
            delta ->
          StrictLess (reals context)
            (distanceE (realSpace (codomain context))
              (f x)
              (f point))
            epsilon))
