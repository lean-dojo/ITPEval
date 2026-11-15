-- Statement-only formalization of thousand-theorems corpus artifact Q1477053,
-- "Arzelà–Ascoli theorem": the uniform closure of a pointwise equicontinuous
-- family of bounded continuous maps from a compact space into a Hausdorff
-- pseudometric space is compact when all values lie in one compact subset.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1477053_arzel_ascoli_theorem where

open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _!=_

data Bottom {a : Level} : Set a where

record Top {a : Level} : Set a where
  constructor top

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} proposition =
  proposition -> Bottom {a}

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

data Member
  {a : Level}
  {A : Set a}
  (x : A) :
  List A ->
  Set a where

  at-head :
    {xs : List A} ->
    Member x (x ∷ xs)

  in-tail :
    {y : A} ->
    {xs : List A} ->
    Member x xs ->
    Member x (y ∷ xs)

-- A complete Archimedean ordered field presents the real line used by
-- Mathlib's real-valued pseudometric spaces.
record RealLine
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zeroR oneR :
      R

    addR multiplyR :
      R ->
      R ->
      R

    negateR reciprocalR :
      R ->
      R

    lessOrEqualR :
      R ->
      R ->
      Set r

    fromNatR :
      Nat ->
      R

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
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)

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

    zero-less-than-oneR :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

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
      Σ Nat
        (\ n ->
          lessOrEqualR x (fromNatR n))

    least-upper-boundR :
      (P : R -> Set r) ->
      Σ R P ->
      Σ R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Σ R
        (\ supremum ->
          Both
            ((x : R) ->
              P x ->
              lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) ->
                P x ->
                lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open RealLine

StrictLess :
  {r : Level} ->
  {R : Set r} ->
  RealLine R ->
  R ->
  R ->
  Set r
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

Positive :
  {r : Level} ->
  {R : Set r} ->
  RealLine R ->
  R ->
  Set r
Positive reals x =
  StrictLess reals (zeroR reals) x

Predicate :
  {a p : Level} ->
  Set a ->
  Set (a ⊔ lsuc p)
Predicate {p = p} X =
  X -> Set p

Whole :
  {a p : Level} ->
  {X : Set a} ->
  Predicate {p = p} X
Whole _ =
  Top

record NeighborhoodRefinement
  {a p : Level}
  {X : Set a}
  (near : X -> Predicate {p = p} X -> Set p)
  (x : X)
  (U : Predicate {p = p} X) :
  Set (a ⊔ lsuc p) where

  field
    refinement :
      Predicate {p = p} X

    refinement-near :
      near x refinement

    refinement-stays-near :
      (y : X) ->
      refinement y ->
      near y U

record TopologicalSpace
  {a p : Level}
  (X : Set a) :
  Set (a ⊔ lsuc p) where

  field
    neighborhood :
      X ->
      Predicate {p = p} X ->
      Set p

    neighborhood-contains :
      (x : X) ->
      (U : Predicate {p = p} X) ->
      neighborhood x U ->
      U x

    neighborhood-whole :
      (x : X) ->
      neighborhood x Whole

    neighborhood-upward :
      (x : X) ->
      (U V : Predicate {p = p} X) ->
      neighborhood x U ->
      ((y : X) -> U y -> V y) ->
      neighborhood x V

    neighborhood-intersection :
      (x : X) ->
      (U V : Predicate {p = p} X) ->
      neighborhood x U ->
      neighborhood x V ->
      neighborhood x
        (\ y ->
          Both (U y) (V y))

    neighborhood-local :
      (x : X) ->
      (U : Predicate {p = p} X) ->
      neighborhood x U ->
      NeighborhoodRefinement neighborhood x U

open TopologicalSpace

IsOpen :
  {a p : Level} ->
  {X : Set a} ->
  TopologicalSpace {p = p} X ->
  Predicate {p = p} X ->
  Set (a ⊔ p)
IsOpen {X = X} topology U =
  (x : X) ->
  U x ->
  neighborhood topology x U

Covers :
  {a p i : Level} ->
  {X : Set a} ->
  {I : Set i} ->
  Predicate {p = p} X ->
  (I -> Predicate {p = p} X) ->
  Set (a ⊔ p ⊔ i)
Covers {X = X} {I = I} U sets =
  (x : X) ->
  U x ->
  Σ I
    (\ index ->
      sets index x)

FiniteSubcover :
  {a p i : Level} ->
  {X : Set a} ->
  {I : Set i} ->
  Predicate {p = p} X ->
  (I -> Predicate {p = p} X) ->
  Set (a ⊔ p ⊔ i)
FiniteSubcover {X = X} {I = I} U sets =
  Σ (List I)
    (\ selected ->
      (x : X) ->
      U x ->
      Σ I
        (\ index ->
          Both
            (Member index selected)
            (sets index x)))

CompactFor :
  {a p o : Level} ->
  {X : Set a} ->
  (Predicate {p = p} X -> Set o) ->
  Predicate {p = p} X ->
  Setω
CompactFor {a = a} {p = p} {X = X} Open U =
  (i : Level) ->
  (I : Set i) ->
  (sets : I -> Predicate {p = p} X) ->
  ((index : I) ->
    Open (sets index)) ->
  Covers {a = a} {p = p} {i = i} U sets ->
  FiniteSubcover {a = a} {p = p} {i = i} U sets

CompactSpace :
  {a p : Level} ->
  {X : Set a} ->
  TopologicalSpace {p = p} X ->
  Setω
CompactSpace topology =
  CompactFor (IsOpen topology) Whole

record PseudoMetricSpace
  {r y : Level}
  {R : Set r}
  (reals : RealLine R)
  (Y : Set y) :
  Set (r ⊔ y) where

  field
    distance :
      Y ->
      Y ->
      R

    distance-nonnegative :
      (x y : Y) ->
      lessOrEqualR reals (zeroR reals) (distance x y)

    distance-self :
      (x : Y) ->
      distance x x == zeroR reals

    distance-symmetric :
      (x y : Y) ->
      distance x y == distance y x

    distance-triangle :
      (x y z : Y) ->
      lessOrEqualR reals
        (distance x z)
        (addR reals (distance x y) (distance y z))

open PseudoMetricSpace

HausdorffPseudoMetric :
  {r y : Level} ->
  {R : Set r} ->
  {Y : Set y} ->
  {reals : RealLine R} ->
  PseudoMetricSpace reals Y ->
  Set (r ⊔ y)
HausdorffPseudoMetric {reals = reals} metric =
  (x y : _) ->
  distance metric x y == zeroR reals ->
  x == y

MetricOpen :
  {r y : Level} ->
  {R : Set r} ->
  {Y : Set y} ->
  (reals : RealLine R) ->
  PseudoMetricSpace reals Y ->
  Predicate {p = r} Y ->
  Set (r ⊔ y)
MetricOpen {R = R} {Y = Y} reals metric U =
  (center : Y) ->
  U center ->
  Σ R
    (\ radius ->
      Both
        (Positive reals radius)
        ((point : Y) ->
          StrictLess reals
            (distance metric point center)
            radius ->
          U point))

MetricCompact :
  {r y : Level} ->
  {R : Set r} ->
  {Y : Set y} ->
  (reals : RealLine R) ->
  (metric : PseudoMetricSpace reals Y) ->
  Predicate {p = r} Y ->
  Setω
MetricCompact reals metric U =
  CompactFor (MetricOpen reals metric) U

ContinuousToMetric :
  {r x y : Level} ->
  {R : Set r} ->
  {X : Set x} ->
  {Y : Set y} ->
  (reals : RealLine R) ->
  TopologicalSpace {p = r} X ->
  PseudoMetricSpace reals Y ->
  (X -> Y) ->
  Set (r ⊔ x)
ContinuousToMetric {R = R} {X = X} reals source metric f =
  (x : X) ->
  (epsilon : R) ->
  Positive reals epsilon ->
  neighborhood source x
    (\ y ->
      StrictLess reals
        (distance metric (f y) (f x))
        epsilon)

BoundedRange :
  {r x y : Level} ->
  {R : Set r} ->
  {X : Set x} ->
  {Y : Set y} ->
  (reals : RealLine R) ->
  PseudoMetricSpace reals Y ->
  (X -> Y) ->
  Set (r ⊔ x)
BoundedRange {R = R} {X = X} reals metric f =
  Σ R
    (\ bound ->
      (x y : X) ->
      lessOrEqualR reals
        (distance metric (f x) (f y))
        bound)

BoundedContinuous :
  {r x y : Level} ->
  {R : Set r} ->
  {X : Set x} ->
  {Y : Set y} ->
  (reals : RealLine R) ->
  TopologicalSpace {p = r} X ->
  PseudoMetricSpace reals Y ->
  (X -> Y) ->
  Set (r ⊔ x)
BoundedContinuous reals source metric f =
  Both
    (ContinuousToMetric reals source metric f)
    (BoundedRange reals metric f)

Equicontinuous :
  {r x y : Level} ->
  {R : Set r} ->
  {X : Set x} ->
  {Y : Set y} ->
  (reals : RealLine R) ->
  TopologicalSpace {p = r} X ->
  PseudoMetricSpace reals Y ->
  Predicate {a = x ⊔ y} {p = r ⊔ x ⊔ y} (X -> Y) ->
  Set (x ⊔ y ⊔ lsuc r)
Equicontinuous
  {r = r} {R = R} {X = X}
  reals source metric family =
  (x : X) ->
  (epsilon : R) ->
  Positive reals epsilon ->
  Σ (Predicate {p = r} X)
    (\ U ->
      Both
        (neighborhood source x U)
        ((f : X -> _) ->
          family f ->
          (y z : X) ->
          U y ->
          U z ->
          StrictLess reals
            (distance metric (f y) (f z))
            epsilon))

UniformClose :
  {r x y : Level} ->
  {R : Set r} ->
  {X : Set x} ->
  {Y : Set y} ->
  (reals : RealLine R) ->
  PseudoMetricSpace reals Y ->
  R ->
  (X -> Y) ->
  (X -> Y) ->
  Set (r ⊔ x)
UniformClose {R = R} {X = X} reals metric epsilon f g =
  Σ R
    (\ margin ->
      Both
        (Positive reals margin)
        ((x : X) ->
          lessOrEqualR reals
            (addR reals
              (distance metric (f x) (g x))
              margin)
            epsilon))

UniformOpen :
  {r x y : Level} ->
  {R : Set r} ->
  {X : Set x} ->
  {Y : Set y} ->
  (reals : RealLine R) ->
  TopologicalSpace {p = r} X ->
  PseudoMetricSpace reals Y ->
  Predicate {a = x ⊔ y} {p = r ⊔ x ⊔ y} (X -> Y) ->
  Set (r ⊔ x ⊔ y)
UniformOpen {R = R} {X = X}
  reals source metric U =
  (f : X -> _) ->
  U f ->
  Both
    (BoundedContinuous reals source metric f)
    (Σ R
      (\ epsilon ->
        Both
          (Positive reals epsilon)
          ((g : X -> _) ->
            BoundedContinuous reals source metric g ->
            UniformClose reals metric epsilon f g ->
            U g)))

UniformClosure :
  {r x y : Level} ->
  {R : Set r} ->
  {X : Set x} ->
  {Y : Set y} ->
  (reals : RealLine R) ->
  TopologicalSpace {p = r} X ->
  PseudoMetricSpace reals Y ->
  Predicate {a = x ⊔ y} {p = r ⊔ x ⊔ y} (X -> Y) ->
  Predicate {a = x ⊔ y} {p = r ⊔ x ⊔ y} (X -> Y)
UniformClosure {R = R} {X = X}
  reals source metric family f =
  Both
    (BoundedContinuous reals source metric f)
    ((epsilon : R) ->
      Positive reals epsilon ->
      Σ (X -> _)
        (\ g ->
          Both
            (family g)
            (UniformClose reals metric epsilon f g)))

arzela-ascoli-theorem : Setω
arzela-ascoli-theorem =
  (r x y : Level) ->
  (R : Set r) ->
  (reals : RealLine R) ->
  (X : Set x) ->
  (source : TopologicalSpace {p = r} X) ->
  CompactSpace source ->
  (Y : Set y) ->
  (metric : PseudoMetricSpace reals Y) ->
  HausdorffPseudoMetric metric ->
  (compactRange : Predicate {p = r} Y) ->
  MetricCompact reals metric compactRange ->
  (family :
    Predicate {a = x ⊔ y} {p = r ⊔ x ⊔ y} (X -> Y)) ->
  ((f : X -> Y) ->
    family f ->
    BoundedContinuous reals source metric f) ->
  ((f : X -> Y) ->
    (point : X) ->
    family f ->
    compactRange (f point)) ->
  Equicontinuous reals source metric family ->
  CompactFor
    (UniformOpen reals source metric)
    (UniformClosure reals source metric family)
