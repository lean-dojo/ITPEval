-- Statement-only formalization of thousand-theorems corpus artifact Q3527166,
-- "Steinhaus theorem": in a locally compact topological group, the quotient
-- set E / E of a measurable positive-measure set is a neighborhood of the
-- identity for an inner-regular Haar measure. This file contains no proof.

{-# OPTIONS --safe #-}

module Q3527166_steinhaus_theorem where

open import Support.Bochner
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open CompleteOrderedField
open SigmaAlgebra
open ExtendedNonnegativeReals
open Measure

record Group (G : Set) : Set1 where
  field
    identity :
      G
    multiply :
      G -> G -> G
    inverse :
      G -> G
    multiply-associative :
      (x y z : G) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    identity-left :
      (x : G) ->
      multiply identity x == x
    identity-right :
      (x : G) ->
      multiply x identity == x
    inverse-left :
      (x : G) ->
      multiply (inverse x) x == identity
    inverse-right :
      (x : G) ->
      multiply x (inverse x) == identity

open Group

record NeighborhoodRefinement
  {G : Set}
  (near : G -> Predicate G -> Set)
  (x : G)
  (U : Predicate G) :
  Set1 where

  field
    refinement :
      Predicate G
    refinement-near :
      near x refinement
    refinement-stays-near :
      (y : G) ->
      refinement y ->
      near y U

record TopologicalSpace (G : Set) : Set2 where
  field
    neighborhood :
      G ->
      Predicate G ->
      Set
    neighborhood-contains :
      (x : G) ->
      (U : Predicate G) ->
      neighborhood x U ->
      U x
    neighborhood-whole :
      (x : G) ->
      neighborhood x wholeSet
    neighborhood-upward :
      (x : G) ->
      (U V : Predicate G) ->
      neighborhood x U ->
      Subset U V ->
      neighborhood x V
    neighborhood-intersection :
      (x : G) ->
      (U V : Predicate G) ->
      neighborhood x U ->
      neighborhood x V ->
      neighborhood x (intersection U V)
    neighborhood-local :
      (x : G) ->
      (U : Predicate G) ->
      neighborhood x U ->
      NeighborhoodRefinement neighborhood x U

open TopologicalSpace

Open :
  {G : Set} ->
  TopologicalSpace G ->
  Predicate G ->
  Set
Open {G = G} topology U =
  (x : G) ->
  U x ->
  neighborhood topology x U

record CoverWitness
  {G : Set}
  (family : Predicate G -> Set)
  (x : G) :
  Set1 where

  field
    member-set :
      Predicate G
    member-is-selected :
      family member-set
    member-contains-point :
      member-set x

data FiniteSubfamily
  {G : Set}
  (family : Predicate G -> Set) :
  Set2 where

  no-sets :
    FiniteSubfamily family

  add-set :
    (U : Predicate G) ->
    family U ->
    FiniteSubfamily family ->
    FiniteSubfamily family

CoveredByFinite :
  {G : Set} ->
  {family : Predicate G -> Set} ->
  FiniteSubfamily family ->
  Predicate G
CoveredByFinite no-sets x =
  Bottom
CoveredByFinite (add-set U selected rest) x =
  Either (U x) (CoveredByFinite rest x)

record FiniteSubcover
  {G : Set}
  (family : Predicate G -> Set)
  (K : Predicate G) :
  Set2 where

  field
    selected-sets :
      FiniteSubfamily family
    selected-sets-cover :
      Subset K (CoveredByFinite selected-sets)

Compact :
  {G : Set} ->
  TopologicalSpace G ->
  Predicate G ->
  Set2
Compact {G = G} topology K =
  (family : Predicate G -> Set) ->
  ((U : Predicate G) ->
    family U ->
    Open topology U) ->
  ((x : G) ->
    K x ->
    CoverWitness family x) ->
  FiniteSubcover family K

record ProductNeighborhood
  {G : Set}
  (group : Group G)
  (topology : TopologicalSpace G)
  (x y : G)
  (W : Predicate G) :
  Set2 where

  field
    left-neighborhood :
      Predicate G
    right-neighborhood :
      Predicate G
    left-is-near :
      neighborhood topology x left-neighborhood
    right-is-near :
      neighborhood topology y right-neighborhood
    products-stay-in-W :
      (u v : G) ->
      left-neighborhood u ->
      right-neighborhood v ->
      W (multiply group u v)

record InverseNeighborhood
  {G : Set}
  (group : Group G)
  (topology : TopologicalSpace G)
  (x : G)
  (W : Predicate G) :
  Set2 where

  field
    source-neighborhood :
      Predicate G
    source-is-near :
      neighborhood topology x source-neighborhood
    inverses-stay-in-W :
      (u : G) ->
      source-neighborhood u ->
      W (inverse group u)

record IsTopologicalGroup
  {G : Set}
  (group : Group G)
  (topology : TopologicalSpace G) :
  Set2 where

  field
    multiplication-continuous :
      (x y : G) ->
      (W : Predicate G) ->
      neighborhood topology (multiply group x y) W ->
      ProductNeighborhood group topology x y W
    inversion-continuous :
      (x : G) ->
      (W : Predicate G) ->
      neighborhood topology (inverse group x) W ->
      InverseNeighborhood group topology x W

data BorelGenerated
  {G : Set}
  (topology : TopologicalSpace G) :
  Predicate G ->
  Set1 where

  borel-open :
    {U : Predicate G} ->
    Open topology U ->
    BorelGenerated topology U

  borel-empty :
    BorelGenerated topology emptySet

  borel-complement :
    {S : Predicate G} ->
    BorelGenerated topology S ->
    BorelGenerated topology (complement S)

  borel-countable-union :
    (sets : Nat -> Predicate G) ->
    ((n : Nat) ->
      BorelGenerated topology (sets n)) ->
    BorelGenerated topology (countableUnion sets)

  borel-congruent :
    {S T : Predicate G} ->
    ((x : G) ->
      Iff (S x) (T x)) ->
    BorelGenerated topology S ->
    BorelGenerated topology T

record BorelSpace
  {G : Set}
  (topology : TopologicalSpace G)
  (events : SigmaAlgebra G) :
  Set2 where

  field
    borel-is-measurable :
      (S : Predicate G) ->
      BorelGenerated topology S ->
      measurable events S
    measurable-is-borel :
      (S : Predicate G) ->
      measurable events S ->
      BorelGenerated topology S

record CompactNeighborhoodWithin
  {G : Set}
  (topology : TopologicalSpace G)
  (x : G)
  (N : Predicate G) :
  Set2 where

  field
    compact-neighborhood :
      Predicate G
    compact-neighborhood-near :
      neighborhood topology x compact-neighborhood
    compact-neighborhood-contained :
      Subset compact-neighborhood N
    compact-neighborhood-compact :
      Compact topology compact-neighborhood

record LocallyCompactSpace
  {G : Set}
  (topology : TopologicalSpace G) :
  Set2 where

  field
    local-compact-neighborhood :
      (x : G) ->
      (N : Predicate G) ->
      neighborhood topology x N ->
      CompactNeighborhoodWithin topology x N

leftTranslate :
  {G : Set} ->
  Group G ->
  G ->
  Predicate G ->
  Predicate G
leftTranslate group g S x =
  S (multiply group (inverse group g) x)

quotientSet :
  {G : Set} ->
  Group G ->
  Predicate G ->
  Predicate G ->
  Predicate G
quotientSet {G = G} group S T z =
  Exists G
    (\ x ->
      Both
        (S x)
        (Exists G
          (\ y ->
            Both
              (T y)
              (z == multiply group x (inverse group y)))))

Nonempty :
  {G : Set} ->
  Predicate G ->
  Set
Nonempty {G = G} S =
  Exists G S

StrictLessM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  M ->
  M ->
  Set
StrictLessM extended x y =
  Both
    (lessOrEqualM extended x y)
    (x != y)

record IsHaarMeasure
  {R M G : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals)
  (group : Group G)
  (topology : TopologicalSpace G)
  {events : SigmaAlgebra G}
  (measure : Measure extended events) :
  Set2 where

  field
    left-invariant :
      (g : G) ->
      (S : Predicate G) ->
      outerMass measure (leftTranslate group g S) ==
      outerMass measure S
    finite-on-compact :
      (K : Predicate G) ->
      Compact topology K ->
      outerMass measure K != infinityM extended
    positive-on-nonempty-open :
      (U : Predicate G) ->
      Open topology U ->
      Nonempty U ->
      outerMass measure U != zeroM extended

record InnerCompactApproximation
  {R M G : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals)
  (topology : TopologicalSpace G)
  {events : SigmaAlgebra G}
  (measure : Measure extended events)
  (U : Predicate G)
  (r : M) :
  Set2 where

  field
    compact-subset :
      Predicate G
    compact-subset-contained :
      Subset compact-subset U
    compact-subset-is-compact :
      Compact topology compact-subset
    compact-subset-mass-above :
      StrictLessM extended r (outerMass measure compact-subset)

record InnerRegular
  {R M G : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals)
  (topology : TopologicalSpace G)
  {events : SigmaAlgebra G}
  (measure : Measure extended events) :
  Set2 where

  field
    inner-regular :
      (U : Predicate G) ->
      measurable events U ->
      (r : M) ->
      StrictLessM extended r (outerMass measure U) ->
      InnerCompactApproximation extended topology measure U r

steinhaus-theorem : Set2
steinhaus-theorem =
  (R M G : Set) ->
  (reals : CompleteOrderedField R) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (group : Group G) ->
  (topology : TopologicalSpace G) ->
  IsTopologicalGroup group topology ->
  (events : SigmaAlgebra G) ->
  BorelSpace topology events ->
  LocallyCompactSpace topology ->
  (measure : Measure extended events) ->
  IsHaarMeasure extended group topology measure ->
  InnerRegular extended topology measure ->
  (E : Predicate G) ->
  measurable events E ->
  StrictLessM extended
    (zeroM extended)
    (outerMass measure E) ->
  neighborhood topology
    (identity group)
    (quotientSet group E E)
