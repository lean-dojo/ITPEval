-- Statement-only formalization of thousand-theorems corpus artifact Q595466,
-- "Dini's theorem": a monotone family of continuous functions into a solid
-- normed lattice ordered additive group that converges pointwise along atTop
-- converges locally uniformly. This file contains no proof.

{-# OPTIONS --safe #-}

module Q595466_dini_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Top : Set where
  constructor top

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

Predicate : Set -> Set1
Predicate A =
  A -> Set

Whole :
  {A : Set} ->
  Predicate A
Whole _ =
  Top

Intersection :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Predicate A
Intersection P Q x =
  Both (P x) (Q x)

Subset :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Set
Subset {A = A} P Q =
  (x : A) ->
  P x ->
  Q x

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR :
      R

    addR multiplyR :
      R ->
      R ->
      R

    negateR reciprocalR absoluteR :
      R ->
      R

    lessOrEqualR :
      R ->
      R ->
      Set

    fromNatR :
      Nat ->
      R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) ->
      addR x y == addR y x

    add-associative :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)

    add-zero :
      (x : R) ->
      addR x zeroR == x

    add-inverse :
      (x : R) ->
      addR x (negateR x) == zeroR

    multiply-commutative :
      (x y : R) ->
      multiplyR x y == multiplyR y x

    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)

    multiply-one :
      (x : R) ->
      multiplyR x oneR == x

    multiply-zero :
      (x : R) ->
      multiplyR x zeroR == zeroR

    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)

    reciprocal-zero :
      reciprocalR zeroR == zeroR

    multiply-reciprocal :
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

    zero-less-than-one :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    absolute-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR (absoluteR x)

    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x

    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x

    absolute-zero-only :
      (x : R) ->
      absoluteR x == zeroR ->
      x == zeroR

    absolute-negate :
      (x : R) ->
      absoluteR (negateR x) == absoluteR x

    absolute-add :
      (x y : R) ->
      lessOrEqualR
        (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y))

    absolute-multiply :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)

    fromNat-zero :
      fromNatR zero == zeroR

    fromNat-successor :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR

    fromNat-injective :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))

    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
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

open CompleteOrderedField

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) :
  Set1 where
  field
    forwardR :
      R ->
      S

    backwardR :
      S ->
      R

    forward-after-backwardR :
      (y : S) ->
      forwardR (backwardR y) == y

    backward-after-forwardR :
      (x : R) ->
      backwardR (forwardR x) == x

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
  (reals : CompleteOrderedField R) :
  Set2 where
  field
    equivalent-complete-ordered-field :
      (S : Set) ->
      (other : CompleteOrderedField S) ->
      CompleteOrderedFieldEquivalence reals other

StrictLessR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLessR reals x y =
  Both (lessOrEqualR reals x y) (x != y)

PositiveR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
PositiveR reals epsilon =
  StrictLessR reals (zeroR reals) epsilon

record Preorder (I : Set) : Set1 where
  field
    lessOrEqualI :
      I ->
      I ->
      Set

    order-reflexiveI :
      (i : I) ->
      lessOrEqualI i i

    order-transitiveI :
      (i j k : I) ->
      lessOrEqualI i j ->
      lessOrEqualI j k ->
      lessOrEqualI i k

open Preorder

-- This inductively generated predicate is membership in the filter generated
-- by all upper rays, hence it also covers empty and nondirected preorders.
data AtTopEventually
  {I : Set}
  (index : Preorder I) :
  Predicate I ->
  Set1 where

  eventually-whole :
    AtTopEventually index Whole

  eventually-upper-ray :
    (cutoff : I) ->
    AtTopEventually index
      (\ i -> lessOrEqualI index cutoff i)

  eventually-upward :
    {P Q : Predicate I} ->
    AtTopEventually index P ->
    Subset P Q ->
    AtTopEventually index Q

  eventually-intersection :
    {P Q : Predicate I} ->
    AtTopEventually index P ->
    AtTopEventually index Q ->
    AtTopEventually index (Intersection P Q)

record NeighborhoodRefinement
  {A : Set}
  (near : A -> Predicate A -> Set)
  (x : A)
  (U : Predicate A) :
  Set1 where
  field
    refinement :
      Predicate A

    refinement-near :
      near x refinement

    refinement-stays-near :
      (y : A) ->
      refinement y ->
      near y U

record TopologicalSpace (A : Set) : Set2 where
  field
    neighborhood :
      A ->
      Predicate A ->
      Set

    neighborhood-contains :
      (x : A) ->
      (U : Predicate A) ->
      neighborhood x U ->
      U x

    neighborhood-whole :
      (x : A) ->
      neighborhood x Whole

    neighborhood-upward :
      (x : A) ->
      (U V : Predicate A) ->
      neighborhood x U ->
      Subset U V ->
      neighborhood x V

    neighborhood-intersection :
      (x : A) ->
      (U V : Predicate A) ->
      neighborhood x U ->
      neighborhood x V ->
      neighborhood x (Intersection U V)

    neighborhood-local :
      (x : A) ->
      (U : Predicate A) ->
      neighborhood x U ->
      NeighborhoodRefinement neighborhood x U

open TopologicalSpace

record NormedLatticeOrderedAddCommGroup
  (R G : Set)
  (reals : CompleteOrderedField R) :
  Set1 where
  field
    zeroG :
      G

    addG :
      G ->
      G ->
      G

    negateG :
      G ->
      G

    normG :
      G ->
      R

    lessOrEqualG :
      G ->
      G ->
      Set

    supG infG :
      G ->
      G ->
      G

    add-commutativeG :
      (x y : G) ->
      addG x y == addG y x

    add-associativeG :
      (x y z : G) ->
      addG (addG x y) z == addG x (addG y z)

    add-zeroG :
      (x : G) ->
      addG x zeroG == x

    add-inverseG :
      (x : G) ->
      addG x (negateG x) == zeroG

    order-reflexiveG :
      (x : G) ->
      lessOrEqualG x x

    order-transitiveG :
      (x y z : G) ->
      lessOrEqualG x y ->
      lessOrEqualG y z ->
      lessOrEqualG x z

    order-antisymmetricG :
      (x y : G) ->
      lessOrEqualG x y ->
      lessOrEqualG y x ->
      x == y

    le-sup-leftG :
      (x y : G) ->
      lessOrEqualG x (supG x y)

    le-sup-rightG :
      (x y : G) ->
      lessOrEqualG y (supG x y)

    sup-leastG :
      (x y z : G) ->
      lessOrEqualG x z ->
      lessOrEqualG y z ->
      lessOrEqualG (supG x y) z

    inf-le-leftG :
      (x y : G) ->
      lessOrEqualG (infG x y) x

    inf-le-rightG :
      (x y : G) ->
      lessOrEqualG (infG x y) y

    inf-greatestG :
      (x y z : G) ->
      lessOrEqualG z x ->
      lessOrEqualG z y ->
      lessOrEqualG z (infG x y)

    add-orderG :
      (x y z : G) ->
      lessOrEqualG x y ->
      lessOrEqualG (addG z x) (addG z y)

    norm-nonnegativeG :
      (x : G) ->
      lessOrEqualR reals (zeroR reals) (normG x)

    norm-zeroG :
      normG zeroG == zeroR reals

    norm-zero-onlyG :
      (x : G) ->
      normG x == zeroR reals ->
      x == zeroG

    norm-negateG :
      (x : G) ->
      normG (negateG x) == normG x

    norm-triangleG :
      (x y : G) ->
      lessOrEqualR reals
        (normG (addG x y))
        (addR reals (normG x) (normG y))

    solid-normG :
      (x y : G) ->
      lessOrEqualG
        (supG x (negateG x))
        (supG y (negateG y)) ->
      lessOrEqualR reals (normG x) (normG y)

open NormedLatticeOrderedAddCommGroup

Distance :
  {R G : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedLatticeOrderedAddCommGroup R G reals ->
  G ->
  G ->
  R
Distance group x y =
  normG group (addG group (negateG group x) y)

Continuous :
  {A R G : Set} ->
  {reals : CompleteOrderedField R} ->
  TopologicalSpace A ->
  NormedLatticeOrderedAddCommGroup R G reals ->
  (A -> G) ->
  Set
Continuous {A = A} {R = R} {reals = reals} topology group function =
  (x : A) ->
  (epsilon : R) ->
  PositiveR reals epsilon ->
  neighborhood topology x
    (\ y ->
      StrictLessR reals
        (Distance group (function y) (function x))
        epsilon)

TendstoAtTop :
  {I R G : Set} ->
  {reals : CompleteOrderedField R} ->
  Preorder I ->
  NormedLatticeOrderedAddCommGroup R G reals ->
  (I -> G) ->
  G ->
  Set1
TendstoAtTop {R = R} {reals = reals} index group values limit =
  (epsilon : R) ->
  PositiveR reals epsilon ->
  AtTopEventually index
    (\ i ->
      StrictLessR reals
        (Distance group (values i) limit)
        epsilon)

record LocallyUniformNeighborhood
  {I A R G : Set}
  {reals : CompleteOrderedField R}
  (index : Preorder I)
  (topology : TopologicalSpace A)
  (group : NormedLatticeOrderedAddCommGroup R G reals)
  (functions : I -> A -> G)
  (limit : A -> G)
  (epsilon : R)
  (x : A) :
  Set1 where
  field
    neighborhood-set :
      Predicate A

    neighborhood-witness :
      neighborhood topology x neighborhood-set

    eventually-close :
      AtTopEventually index
        (\ i ->
          (y : A) ->
          neighborhood-set y ->
          StrictLessR reals
            (Distance group (limit y) (functions i y))
            epsilon)

TendstoLocallyUniformlyAtTop :
  {I A R G : Set} ->
  {reals : CompleteOrderedField R} ->
  Preorder I ->
  TopologicalSpace A ->
  NormedLatticeOrderedAddCommGroup R G reals ->
  (I -> A -> G) ->
  (A -> G) ->
  Set1
TendstoLocallyUniformlyAtTop
  {I = I} {A = A} {R = R}
  {reals = reals}
  index topology group functions limit =
  (epsilon : R) ->
  PositiveR reals epsilon ->
  (x : A) ->
  LocallyUniformNeighborhood
    index topology group functions limit epsilon x

dini-s-theorem : Set2
dini-s-theorem =
  (I A R G : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (index : Preorder I) ->
  (topology : TopologicalSpace A) ->
  (group : NormedLatticeOrderedAddCommGroup R G reals) ->
  (functions : I -> A -> G) ->
  (limit : A -> G) ->
  ((i : I) -> Continuous topology group (functions i)) ->
  ((i j : I) ->
    lessOrEqualI index i j ->
    (x : A) ->
    lessOrEqualG group (functions i x) (functions j x)) ->
  Continuous topology group limit ->
  ((x : A) ->
    TendstoAtTop index group
      (\ i -> functions i x)
      (limit x)) ->
  TendstoLocallyUniformlyAtTop
    index topology group functions limit
