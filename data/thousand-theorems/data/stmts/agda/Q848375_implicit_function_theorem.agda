-- Statement-only formalization of thousand-theorems corpus artifact Q848375,
-- "Implicit function theorem": two strictly differentiable maps with
-- surjective derivatives and complementary kernels admit a local implicit
-- function inverse to their product map. This file contains no proof.

{-# OPTIONS --safe #-}

module Q848375_implicit_function_theorem where

open import Support.Q931001_inverse_function_theorem
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

open CompleteOrderedField
open NontriviallyNormedField
open NormedSpace
open ContinuousLinearMap

SurjectiveLinear :
  {K R E F : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  {domain : NormedSpace K R E reals scalars} ->
  {codomain : NormedSpace K R F reals scalars} ->
  ContinuousLinearMap domain codomain ->
  Set
SurjectiveLinear {E = E} {F = F} linear =
  (y : F) ->
  Exists E
    (\ x ->
      apply linear x == y)

record ComplementaryKernels
  {K R E F G : Set}
  {reals : CompleteOrderedField R}
  {scalars : NontriviallyNormedField K R reals}
  (domain : NormedSpace K R E reals scalars)
  (leftCodomain : NormedSpace K R F reals scalars)
  (rightCodomain : NormedSpace K R G reals scalars)
  (leftDerivative : ContinuousLinearMap domain leftCodomain)
  (rightDerivative : ContinuousLinearMap domain rightCodomain) :
  Set where

  field
    kernels-disjoint :
      (x : E) ->
      apply leftDerivative x == zeroE leftCodomain ->
      apply rightDerivative x == zeroE rightCodomain ->
      x == zeroE domain

    kernels-span :
      (x : E) ->
      Exists E
        (\ leftKernelPart ->
          Exists E
            (\ rightKernelPart ->
              Both
                (Both
                  (apply leftDerivative leftKernelPart ==
                    zeroE leftCodomain)
                  (apply rightDerivative rightKernelPart ==
                    zeroE rightCodomain))
                (x ==
                  addE domain leftKernelPart rightKernelPart)))

record ImplicitFunctionData
  (K R E F G : Set)
  (reals : CompleteOrderedField R)
  (scalars : NontriviallyNormedField K R reals)
  (domain : NormedSpace K R E reals scalars)
  (leftCodomain : NormedSpace K R F reals scalars)
  (rightCodomain : NormedSpace K R G reals scalars) :
  Set1 where

  field
    domain-complete :
      Complete reals (distanceE domain)
    left-codomain-complete :
      Complete reals (distanceE leftCodomain)
    right-codomain-complete :
      Complete reals (distanceE rightCodomain)

    leftFunction :
      E -> F
    leftDerivative :
      ContinuousLinearMap domain leftCodomain
    rightFunction :
      E -> G
    rightDerivative :
      ContinuousLinearMap domain rightCodomain
    point :
      E

    left-strict-derivative :
      HasStrictFDerivAt
        domain leftCodomain
        leftFunction leftDerivative point
    right-strict-derivative :
      HasStrictFDerivAt
        domain rightCodomain
        rightFunction rightDerivative point

    left-derivative-surjective :
      SurjectiveLinear leftDerivative
    right-derivative-surjective :
      SurjectiveLinear rightDerivative
    derivative-kernels-complementary :
      ComplementaryKernels
        domain leftCodomain rightCodomain
        leftDerivative rightDerivative

open ImplicitFunctionData

-- A max-norm product ball around the image of the distinguished point.
-- Positive-radius product balls are open in the product norm topology.

ProductNeighborhood :
  {K R E F G : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  {domain : NormedSpace K R E reals scalars} ->
  {leftCodomain : NormedSpace K R F reals scalars} ->
  {rightCodomain : NormedSpace K R G reals scalars} ->
  ImplicitFunctionData
    K R E F G reals scalars
    domain leftCodomain rightCodomain ->
  R ->
  F ->
  G ->
  Set
ProductNeighborhood
  {reals = reals}
  {leftCodomain = leftCodomain}
  {rightCodomain = rightCodomain}
  implicitData radius y z =
  Both
    (StrictLess reals
      (distanceE leftCodomain y
        (leftFunction implicitData (point implicitData)))
      radius)
    (StrictLess reals
      (distanceE rightCodomain z
        (rightFunction implicitData (point implicitData)))
      radius)

-- The source of the restricted chart is the range of the inverse on the
-- chosen target neighborhood. This avoids quantifying over Set-valued
-- predicates while retaining an arbitrary open source, rather than forcing
-- the source itself to be a norm ball.

SourceOfInverse :
  {K R E F G : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  {domain : NormedSpace K R E reals scalars} ->
  {leftCodomain : NormedSpace K R F reals scalars} ->
  {rightCodomain : NormedSpace K R G reals scalars} ->
  (implicitData :
    ImplicitFunctionData
      K R E F G reals scalars
      domain leftCodomain rightCodomain) ->
  (F -> G -> E) ->
  R ->
  E ->
  Set
SourceOfInverse {F = F} {G = G}
  implicitData implicitFunction targetRadius x =
  Exists F
    (\ y ->
      Exists G
        (\ z ->
          Both
            (ProductNeighborhood implicitData targetRadius y z)
            (implicitFunction y z == x)))

SourceIsOpen :
  {K R E F G : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  {domain : NormedSpace K R E reals scalars} ->
  {leftCodomain : NormedSpace K R F reals scalars} ->
  {rightCodomain : NormedSpace K R G reals scalars} ->
  (implicitData :
    ImplicitFunctionData
      K R E F G reals scalars
      domain leftCodomain rightCodomain) ->
  (F -> G -> E) ->
  R ->
  Set
SourceIsOpen
  {R = R} {reals = reals} {domain = domain}
  implicitData implicitFunction targetRadius =
  (x : _) ->
  SourceOfInverse implicitData implicitFunction targetRadius x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((x' : _) ->
          StrictLess reals (distanceE domain x' x) radius ->
          SourceOfInverse
            implicitData implicitFunction targetRadius x'))

ForwardContinuousOnSource :
  {K R E F G : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  {domain : NormedSpace K R E reals scalars} ->
  {leftCodomain : NormedSpace K R F reals scalars} ->
  {rightCodomain : NormedSpace K R G reals scalars} ->
  (implicitData :
    ImplicitFunctionData
      K R E F G reals scalars
      domain leftCodomain rightCodomain) ->
  (F -> G -> E) ->
  R ->
  Set
ForwardContinuousOnSource
  {R = R} {reals = reals}
  {domain = domain}
  {leftCodomain = leftCodomain}
  {rightCodomain = rightCodomain}
  implicitData implicitFunction targetRadius =
  (x : _) ->
  SourceOfInverse implicitData implicitFunction targetRadius x ->
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((x' : _) ->
          SourceOfInverse
            implicitData implicitFunction targetRadius x' ->
          StrictLess reals (distanceE domain x' x) delta ->
          Both
            (StrictLess reals
              (distanceE leftCodomain
                (leftFunction implicitData x')
                (leftFunction implicitData x))
              epsilon)
            (StrictLess reals
              (distanceE rightCodomain
                (rightFunction implicitData x')
                (rightFunction implicitData x))
              epsilon)))

InverseContinuousOnTarget :
  {K R E F G : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  {domain : NormedSpace K R E reals scalars} ->
  {leftCodomain : NormedSpace K R F reals scalars} ->
  {rightCodomain : NormedSpace K R G reals scalars} ->
  (implicitData :
    ImplicitFunctionData
      K R E F G reals scalars
      domain leftCodomain rightCodomain) ->
  (F -> G -> E) ->
  R ->
  Set
InverseContinuousOnTarget
  {R = R} {reals = reals}
  {domain = domain}
  {leftCodomain = leftCodomain}
  {rightCodomain = rightCodomain}
  implicitData implicitFunction targetRadius =
  (y : _) ->
  (z : _) ->
  ProductNeighborhood implicitData targetRadius y z ->
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((y' : _) ->
          (z' : _) ->
          ProductNeighborhood implicitData targetRadius y' z' ->
          StrictLess reals (distanceE leftCodomain y' y) delta ->
          StrictLess reals (distanceE rightCodomain z' z) delta ->
          StrictLess reals
            (distanceE domain
              (implicitFunction y' z')
              (implicitFunction y z))
            epsilon))

record IsImplicitFunction
  {K R E F G : Set}
  {reals : CompleteOrderedField R}
  {scalars : NontriviallyNormedField K R reals}
  {domain : NormedSpace K R E reals scalars}
  {leftCodomain : NormedSpace K R F reals scalars}
  {rightCodomain : NormedSpace K R G reals scalars}
  (implicitData :
    ImplicitFunctionData
      K R E F G reals scalars
      domain leftCodomain rightCodomain)
  (implicitFunction : F -> G -> E) :
  Set where

  field
    target-radius :
      R
    target-radius-positive :
      Positive reals target-radius
    base-point-in-target :
      ProductNeighborhood implicitData target-radius
        (leftFunction implicitData (point implicitData))
        (rightFunction implicitData (point implicitData))
    point-in-source :
      SourceOfInverse
        implicitData implicitFunction target-radius
        (point implicitData)
    source-open :
      SourceIsOpen implicitData implicitFunction target-radius
    forward-maps-source :
      (x : E) ->
      SourceOfInverse implicitData implicitFunction target-radius x ->
      ProductNeighborhood implicitData target-radius
        (leftFunction implicitData x)
        (rightFunction implicitData x)
    inverse-maps-target :
      (y : F) ->
      (z : G) ->
      ProductNeighborhood implicitData target-radius y z ->
      SourceOfInverse implicitData implicitFunction target-radius
        (implicitFunction y z)
    left-inverse-on-source :
      (x : E) ->
      SourceOfInverse implicitData implicitFunction target-radius x ->
      implicitFunction
        (leftFunction implicitData x)
        (rightFunction implicitData x)
      ==
      x
    right-inverse-on-target :
      (y : F) ->
      (z : G) ->
      ProductNeighborhood implicitData target-radius y z ->
      Both
        (leftFunction implicitData (implicitFunction y z) == y)
        (rightFunction implicitData (implicitFunction y z) == z)
    forward-continuous-on-source :
      ForwardContinuousOnSource
        implicitData implicitFunction target-radius
    inverse-continuous-on-target :
      InverseContinuousOnTarget
        implicitData implicitFunction target-radius

implicit-function-theorem : Set1
implicit-function-theorem =
  (R K E F G : Set) ->
  (reals : CompleteOrderedField R) ->
  (scalars : NontriviallyNormedField K R reals) ->
  (domain : NormedSpace K R E reals scalars) ->
  (leftCodomain : NormedSpace K R F reals scalars) ->
  (rightCodomain : NormedSpace K R G reals scalars) ->
  (implicitData :
    ImplicitFunctionData
      K R E F G reals scalars
      domain leftCodomain rightCodomain) ->
  Exists (F -> G -> E)
    (\ implicitFunction ->
      IsImplicitFunction implicitData implicitFunction)
