-- Statement-only formalization of thousand-theorems corpus artifact Q530152,
-- "Picard&ndash;Lindelöf theorem": under the Picard-Lindelöf conditions on a
-- time-dependent vector field in a real Banach space, a local integral curve
-- exists with the prescribed initial value. This file contains no proof.

{-# OPTIONS --safe #-}

module Q530152_picard_ndash_lindel_f_theorem where

open import Support.Bochner
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

open CompleteOrderedField
open NormedVectorSpace

record NonnegativeReal
  {R : Set}
  (reals : CompleteOrderedField R) : Set where
  constructor nonnegative-real
  field
    nonnegative-value :
      R
    value-nonnegative :
      lessOrEqualR reals
        (zeroR reals)
        nonnegative-value

open NonnegativeReal

ClosedInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Predicate R
ClosedInterval reals lower upper point =
  Both
    (lessOrEqualR reals lower point)
    (lessOrEqualR reals point upper)

ClosedBall :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  E ->
  NonnegativeReal reals ->
  Predicate E
ClosedBall {reals = reals} space center radius point =
  lessOrEqualR reals
    (distanceE space point center)
    (nonnegative-value radius)

maximumR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
maximumR reals x y with order-total reals x y
... | left _ = y
... | right _ = x

LipschitzOnWith :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  NonnegativeReal reals ->
  (E -> E) ->
  Predicate E ->
  Set
LipschitzOnWith {reals = reals} space constant function domain =
  (x y : _) ->
  domain x ->
  domain y ->
  lessOrEqualR reals
    (distanceE space (function x) (function y))
    (multiplyR reals
      (nonnegative-value constant)
      (distanceE space x y))

ContinuousWithinAt :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  NormedVectorSpace R E reals ->
  (R -> E) ->
  Predicate R ->
  R ->
  Set
ContinuousWithinAt {R = R} reals space function domain point =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((y : R) ->
          domain y ->
          StrictLess reals (distanceR reals y point) delta ->
          StrictLess reals
            (distanceE space (function y) (function point))
            epsilon))

ContinuousOn :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  NormedVectorSpace R E reals ->
  (R -> E) ->
  Predicate R ->
  Set
ContinuousOn reals space function domain =
  (point : _) ->
  domain point ->
  ContinuousWithinAt reals space function domain point

DerivativeRemainder :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  (R -> E) ->
  E ->
  R ->
  R ->
  E
DerivativeRemainder {reals = reals}
  space function derivative point y =
  subtractE space
    (subtractE space (function y) (function point))
    (scaleE space
      (subtractR reals y point)
      derivative)

HasDerivWithinAt :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  NormedVectorSpace R E reals ->
  (R -> E) ->
  E ->
  Predicate R ->
  R ->
  Set
HasDerivWithinAt {R = R} reals space function derivative domain point =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((y : R) ->
          domain y ->
          StrictLess reals (distanceR reals y point) delta ->
          lessOrEqualR reals
            (normE space
              (DerivativeRemainder
                space function derivative point y))
            (multiplyR reals epsilon
              (distanceR reals y point))))

record IsPicardLindelof
  {R E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (f : R -> E -> E)
  (tmin tmax t0 : R)
  (x0 : E)
  (a r L K : NonnegativeReal reals) : Set1 where
  field
    lipschitz-in-space :
      (time : R) ->
      ClosedInterval reals tmin tmax time ->
      LipschitzOnWith space K (f time) (ClosedBall space x0 a)

    continuous-in-time :
      (point : E) ->
      ClosedBall space x0 a point ->
      ContinuousOn reals space
        (\ time -> f time point)
        (ClosedInterval reals tmin tmax)

    norm-bound :
      (time : R) ->
      ClosedInterval reals tmin tmax time ->
      (point : E) ->
      ClosedBall space x0 a point ->
      lessOrEqualR reals
        (normE space (f time point))
        (nonnegative-value L)

    time-radius-bound :
      lessOrEqualR reals
        (multiplyR reals
          (nonnegative-value L)
          (maximumR reals
            (subtractR reals tmax t0)
            (subtractR reals t0 tmin)))
        (subtractR reals
          (nonnegative-value a)
          (nonnegative-value r))

picard-lindelof-theorem : Set1
picard-lindelof-theorem =
  (R E : Set) ->
  (reals : CompleteOrderedField R) ->
  (space : NormedVectorSpace R E reals) ->
  Complete reals (distanceE space) ->
  (f : R -> E -> E) ->
  (tmin tmax t0 : R) ->
  ClosedInterval reals tmin tmax t0 ->
  (x0 x : E) ->
  (a r L K : NonnegativeReal reals) ->
  IsPicardLindelof reals space f tmin tmax t0 x0 a r L K ->
  ClosedBall space x0 r x ->
  Exists (R -> E)
    (\ curve ->
      Both
        (curve t0 == x)
        ((time : R) ->
          ClosedInterval reals tmin tmax time ->
          HasDerivWithinAt reals space
            curve
            (f time (curve time))
            (ClosedInterval reals tmin tmax)
            time))
