-- Statement-only formalization of thousand-theorems corpus artifact Q1306095,
-- "Whitney embedding theorem": every compact Hausdorff smooth real manifold
-- modeled on a finite-dimensional normed space admits a smooth closed embedding
-- into some Euclidean space with injective differential. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1306095_whitney_embedding_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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

record MixedIff (A : Set) (B : Set1) : Set1 where
  constructor mixed-equivalence
  field
    forward-mixed  : A -> B
    backward-mixed : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data Member {A : Set} (x : A) : List A -> Set where
  at-head : {xs : List A} -> Member x (x ∷ xs)
  in-tail : {y : A} {xs : List A} -> Member x xs -> Member x (y ∷ xs)

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR absoluteR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> addR x y == addR y x
    add-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    add-zero :
      (x : R) -> addR x zeroR == x
    add-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) -> multiplyR x oneR == x
    multiply-zero :
      (x : R) -> multiplyR x zeroR == zeroR
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

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-one :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    absolute-nonnegative :
      (x : R) -> lessOrEqualR zeroR (absoluteR x)
    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x
    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x
    absolute-zero-only :
      (x : R) -> absoluteR x == zeroR -> x == zeroR
    absolute-negate :
      (x : R) -> absoluteR (negateR x) == absoluteR x
    absolute-add :
      (x y : R) ->
      lessOrEqualR (absoluteR (addR x y))
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
          (x : R) -> P x -> lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) : Set1 where
  field
    forwardR : R -> S
    backwardR : S -> R
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
      forwardR (negateR source x) == negateR target (forwardR x)
    forward-reciprocalR :
      (x : R) ->
      forwardR (reciprocalR source x) ==
      reciprocalR target (forwardR x)
    forward-absoluteR :
      (x : R) ->
      forwardR (absoluteR source x) == absoluteR target (forwardR x)
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

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

record NormedVectorSpace
  (R E : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : R -> E -> E
    normE : E -> R

    add-commutativeE :
      (x y : E) -> addE x y == addE y x
    add-associativeE :
      (x y z : E) -> addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) -> addE x zeroE == x
    add-inverseE :
      (x : E) -> addE x (negateE x) == zeroE

    scale-one :
      (x : E) -> scaleE (oneR reals) x == x
    scale-associative :
      (a b : R) ->
      (x : E) ->
      scaleE (multiplyR reals a b) x == scaleE a (scaleE b x)
    scale-add-vectors :
      (a : R) ->
      (x y : E) ->
      scaleE a (addE x y) == addE (scaleE a x) (scaleE a y)
    scale-add-scalars :
      (a b : R) ->
      (x : E) ->
      scaleE (addR reals a b) x == addE (scaleE a x) (scaleE b x)

    norm-nonnegative :
      (x : E) -> lessOrEqualR reals (zeroR reals) (normE x)
    norm-zero :
      normE zeroE == zeroR reals
    norm-zero-only :
      (x : E) -> normE x == zeroR reals -> x == zeroE
    norm-negate :
      (x : E) -> normE (negateE x) == normE x
    norm-add :
      (x y : E) ->
      lessOrEqualR reals (normE (addE x y))
        (addR reals (normE x) (normE y))
    norm-scale :
      (a : R) ->
      (x : E) ->
      normE (scaleE a x) ==
      multiplyR reals (absoluteR reals a) (normE x)

open NormedVectorSpace

subtractE :
  {R E : Set}
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  E ->
  E ->
  E
subtractE space x y =
  addE space x (negateE space y)

distanceE :
  {R E : Set}
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  E ->
  E ->
  R
distanceE space x y =
  normE space (subtractE space x y)

Vector : Set -> Nat -> Set
Vector R n =
  Fin n -> R

VectorEqual :
  {R : Set}
  {n : Nat} ->
  Vector R n ->
  Vector R n ->
  Set
VectorEqual {n = n} x y =
  (i : Fin n) -> x i == y i

vectorAdd :
  {R : Set}
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Vector R n
vectorAdd reals x y i =
  addR reals (x i) (y i)

vectorSubtract :
  {R : Set}
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Vector R n
vectorSubtract reals x y i =
  subtractR reals (x i) (y i)

vectorScale :
  {R : Set}
  {n : Nat} ->
  CompleteOrderedField R ->
  R ->
  Vector R n ->
  Vector R n
vectorScale reals scalar x i =
  multiplyR reals scalar (x i)

vectorNorm :
  {R : Set} ->
  CompleteOrderedField R ->
  (n : Nat) ->
  Vector R n ->
  R
vectorNorm reals zero x =
  zeroR reals
vectorNorm reals (suc n) x =
  addR reals
    (absoluteR reals (x fzero))
    (vectorNorm reals n (\ i -> x (fsuc i)))

vectorDistance :
  {R : Set}
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  R
vectorDistance {n = n} reals x y =
  vectorNorm reals n (vectorSubtract reals x y)

record LinearEquivalence
  {R E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (n : Nat) : Set1 where
  field
    forward-linear : E -> Vector R n
    backward-linear : Vector R n -> E
    forward-after-backward :
      (x : Vector R n) ->
      VectorEqual (forward-linear (backward-linear x)) x
    backward-after-forward :
      (x : E) ->
      backward-linear (forward-linear x) == x
    forward-add :
      (x y : E) ->
      VectorEqual
        (forward-linear (addE space x y))
        (vectorAdd reals (forward-linear x) (forward-linear y))
    forward-scale :
      (a : R) ->
      (x : E) ->
      VectorEqual
        (forward-linear (scaleE space a x))
        (vectorScale reals a (forward-linear x))

record FiniteDimensional
  {R E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals) : Set1 where
  field
    dimension : Nat
    linear-equivalence :
      LinearEquivalence reals space dimension

Predicate : Set -> Set1
Predicate A =
  A -> Set

emptySet :
  {A : Set} ->
  Predicate A
emptySet _ =
  Bottom

wholeSet :
  {A : Set} ->
  Predicate A
wholeSet _ =
  Top

record TopologicalSpace (X : Set) : Set1 where
  field
    Open : Predicate X -> Set
    open-empty :
      Open emptySet
    open-whole :
      Open wholeSet
    open-intersection :
      (U V : Predicate X) ->
      Open U ->
      Open V ->
      Open (\ x -> Both (U x) (V x))
    open-arbitrary-union :
      (I : Set) ->
      (family : I -> Predicate X) ->
      ((i : I) -> Open (family i)) ->
      Open (\ x -> Exists I (\ i -> family i x))

open TopologicalSpace

NormOpen :
  {R E : Set}
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  Predicate E ->
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

VectorOpen :
  {R : Set} ->
  CompleteOrderedField R ->
  (n : Nat) ->
  Predicate (Vector R n) ->
  Set
VectorOpen reals n U =
  (x : Vector _ n) ->
  U x ->
  Exists _
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : Vector _ n) ->
          StrictLess reals (vectorDistance reals y x) radius ->
          U y))

record RelativelyOpen
  {R E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedVectorSpace R E reals)
  (carrier U : Predicate E) : Set1 where
  field
    ambient-open-set :
      Predicate E
    ambient-is-open :
      NormOpen space ambient-open-set
    relative-characterization :
      (x : E) ->
      Iff
        (U x)
        (Both (carrier x) (ambient-open-set x))

Compact :
  {X : Set} ->
  TopologicalSpace X ->
  Set1
Compact {X} topology =
  (I : Set) ->
  (cover : I -> Predicate X) ->
  ((i : I) -> Open topology (cover i)) ->
  ((x : X) -> Exists I (\ i -> cover i x)) ->
  Exists (List I)
    (\ chosen ->
      (x : X) ->
      Exists I
        (\ i ->
          Both
            (Member i chosen)
            (cover i x)))

record SeparatedNeighborhoods
  {X : Set}
  (topology : TopologicalSpace X)
  (x y : X) : Set1 where
  field
    left-neighborhood :
      Predicate X
    right-neighborhood :
      Predicate X
    left-open :
      Open topology left-neighborhood
    right-open :
      Open topology right-neighborhood
    left-contains :
      left-neighborhood x
    right-contains :
      right-neighborhood y
    neighborhoods-disjoint :
      (z : X) ->
      left-neighborhood z ->
      right-neighborhood z ->
      Bottom

Hausdorff :
  {X : Set} ->
  TopologicalSpace X ->
  Set1
Hausdorff {X} topology =
  (x y : X) ->
  x != y ->
  SeparatedNeighborhoods topology x y

Continuous :
  {X Y : Set} ->
  TopologicalSpace X ->
  TopologicalSpace Y ->
  (X -> Y) ->
  Set1
Continuous source target f =
  (U : Predicate _) ->
  Open target U ->
  Open source (\ x -> U (f x))

Directions : Set -> Nat -> Set
Directions E n =
  Fin n -> E

prependDirection :
  {E : Set}
  {n : Nat} ->
  E ->
  Directions E n ->
  Directions E (suc n)
prependDirection x directions fzero =
  x
prependDirection x directions (fsuc i) =
  directions i

singleDirection :
  {E : Set} ->
  E ->
  Directions E (suc zero)
singleDirection x fzero =
  x

DirectionalDerivativeAtE :
  {R E : Set}
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  (E -> E) ->
  E ->
  E ->
  E ->
  Set
DirectionalDerivativeAtE {R} {E} {reals} space f point direction derivative =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((t : R) ->
          Positive reals (absoluteR reals t) ->
          StrictLess reals (absoluteR reals t) delta ->
          StrictLess reals
            (distanceE space
              (scaleE space
                (reciprocalR reals t)
                (subtractE space
                  (f (addE space point (scaleE space t direction)))
                  (f point)))
              derivative)
            epsilon))

DirectionalDerivativeAtVector :
  {R E : Set}
  {reals : CompleteOrderedField R}
  {n : Nat} ->
  (space : NormedVectorSpace R E reals) ->
  (E -> Vector R n) ->
  E ->
  E ->
  Vector R n ->
  Set
DirectionalDerivativeAtVector {R} {E} {reals} {n}
  space f point direction derivative =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((t : R) ->
          Positive reals (absoluteR reals t) ->
          StrictLess reals (absoluteR reals t) delta ->
          StrictLess reals
            (vectorDistance reals
              (vectorScale reals
                (reciprocalR reals t)
                (vectorSubtract reals
                  (f (addE space point (scaleE space t direction)))
                  (f point)))
              derivative)
            epsilon))

record SmoothFunctionE
  {R E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (f : E -> E) : Set1 where
  field
    derivativesE :
      (order : Nat) ->
      E ->
      Directions E order ->
      E
    derivative-zeroE :
      (x : E) ->
      (directions : Directions E zero) ->
      derivativesE zero x directions == f x
    derivative-stepE :
      (order : Nat) ->
      (x direction : E) ->
      (directions : Directions E order) ->
      DirectionalDerivativeAtE space
        (\ y -> derivativesE order y directions)
        x
        direction
        (derivativesE (suc order) x
          (prependDirection direction directions))
    derivatives-continuousE :
      (order : Nat) ->
      (x : E) ->
      (directions : Directions E order) ->
      (epsilon : R) ->
      Positive reals epsilon ->
      Exists R
        (\ delta ->
          Both
            (Positive reals delta)
            ((y : E) ->
              StrictLess reals (distanceE space y x) delta ->
              (otherDirections : Directions E order) ->
              ((i : Fin order) ->
                StrictLess reals
                  (distanceE space (otherDirections i) (directions i))
                  delta) ->
              StrictLess reals
                (distanceE space
                  (derivativesE order y otherDirections)
                  (derivativesE order x directions))
                epsilon))

open SmoothFunctionE

record SmoothFunctionVector
  {R E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  {n : Nat}
  (f : E -> Vector R n) : Set1 where
  field
    derivativesVector :
      (order : Nat) ->
      E ->
      Directions E order ->
      Vector R n
    derivative-zeroVector :
      (x : E) ->
      (directions : Directions E zero) ->
      VectorEqual (derivativesVector zero x directions) (f x)
    derivative-stepVector :
      (order : Nat) ->
      (x direction : E) ->
      (directions : Directions E order) ->
      DirectionalDerivativeAtVector space
        (\ y -> derivativesVector order y directions)
        x
        direction
        (derivativesVector (suc order) x
          (prependDirection direction directions))
    derivatives-continuousVector :
      (order : Nat) ->
      (x : E) ->
      (directions : Directions E order) ->
      (epsilon : R) ->
      Positive reals epsilon ->
      Exists R
        (\ delta ->
          Both
            (Positive reals delta)
            ((y : E) ->
              StrictLess reals (distanceE space y x) delta ->
              (otherDirections : Directions E order) ->
              ((i : Fin order) ->
                StrictLess reals
                  (distanceE space (otherDirections i) (directions i))
                  delta) ->
              StrictLess reals
                (vectorDistance reals
                  (derivativesVector order y otherDirections)
                  (derivativesVector order x directions))
                epsilon))

open SmoothFunctionVector

firstDerivativeE :
  {R E : Set}
  {reals : CompleteOrderedField R}
  {space : NormedVectorSpace R E reals}
  {f : E -> E} ->
  SmoothFunctionE reals space f ->
  E ->
  E ->
  E
firstDerivativeE smooth point direction =
  derivativesE smooth (suc zero) point (singleDirection direction)

firstDerivativeVector :
  {R E : Set}
  {reals : CompleteOrderedField R}
  {space : NormedVectorSpace R E reals}
  {n : Nat}
  {f : E -> Vector R n} ->
  SmoothFunctionVector reals space f ->
  E ->
  E ->
  Vector R n
firstDerivativeVector smooth point direction =
  derivativesVector smooth (suc zero) point (singleDirection direction)

LocallyAgreeE :
  {R E : Set}
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  Predicate E ->
  (E -> E) ->
  (E -> E) ->
  E ->
  Set
LocallyAgreeE {R} {reals = reals} space domain f g point =
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : _) ->
          domain y ->
          StrictLess reals (distanceE space y point) radius ->
          f y == g y))

LocallyAgreeVector :
  {R E : Set}
  {reals : CompleteOrderedField R}
  {n : Nat} ->
  (space : NormedVectorSpace R E reals) ->
  Predicate E ->
  (E -> Vector R n) ->
  (E -> Vector R n) ->
  E ->
  Set
LocallyAgreeVector {R} {reals = reals} space domain f g point =
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : _) ->
          domain y ->
          StrictLess reals (distanceE space y point) radius ->
          VectorEqual (f y) (g y)))

record ModelWithCorners
  {R E H : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (topologyH : TopologicalSpace H) : Set2 where
  field
    carrier : Predicate E
    toModel : H -> E
    fromModel : E -> H
    toModel-in-carrier :
      (x : H) ->
      carrier (toModel x)
    from-to-model :
      (x : H) ->
      fromModel (toModel x) == x
    to-from-model :
      (x : E) ->
      carrier x ->
      toModel (fromModel x) == x
    carrier-convex :
      (x y : E) ->
      carrier x ->
      carrier y ->
      (t : R) ->
      lessOrEqualR reals (zeroR reals) t ->
      lessOrEqualR reals t (oneR reals) ->
      carrier
        (addE space
          (scaleE space t x)
          (scaleE space
            (addR reals (oneR reals) (negateR reals t))
            y))
    carrier-interior-nonempty :
      Exists E
        (\ center ->
          Both
            (carrier center)
            (Exists R
              (\ radius ->
                Both
                  (Positive reals radius)
                  ((point : E) ->
                    StrictLess reals
                      (distanceE space point center)
                      radius ->
                    carrier point))))
    model-topology :
      (U : Predicate H) ->
      MixedIff
        (Open topologyH U)
        (RelativelyOpen space carrier
          (\ x -> Both (carrier x) (U (fromModel x))))
    unique-differentialE :
      (f g : E -> E) ->
      (smoothF : SmoothFunctionE reals space f) ->
      (smoothG : SmoothFunctionE reals space g) ->
      (point : E) ->
      carrier point ->
      LocallyAgreeE space carrier f g point ->
      (direction : E) ->
      firstDerivativeE smoothF point direction ==
      firstDerivativeE smoothG point direction
    unique-differentialVector :
      (n : Nat) ->
      (f g : E -> Vector R n) ->
      (smoothF : SmoothFunctionVector reals space f) ->
      (smoothG : SmoothFunctionVector reals space g) ->
      (point : E) ->
      carrier point ->
      LocallyAgreeVector space carrier f g point ->
      (direction : E) ->
      VectorEqual
        (firstDerivativeVector smoothF point direction)
        (firstDerivativeVector smoothG point direction)

open ModelWithCorners

record ChartedSpace
  {H M : Set}
  (topologyH : TopologicalSpace H)
  (topologyM : TopologicalSpace M) : Set2 where
  field
    Chart : Set
    source : Chart -> Predicate M
    target : Chart -> Predicate H
    toChart : Chart -> M -> H
    fromChart : Chart -> H -> M
    source-open :
      (chart : Chart) ->
      Open topologyM (source chart)
    target-open :
      (chart : Chart) ->
      Open topologyH (target chart)
    chart-cover :
      (x : M) ->
      Exists Chart (\ chart -> source chart x)
    toChart-in-target :
      (chart : Chart) ->
      (x : M) ->
      source chart x ->
      target chart (toChart chart x)
    fromChart-in-source :
      (chart : Chart) ->
      (x : H) ->
      target chart x ->
      source chart (fromChart chart x)
    from-to-chart :
      (chart : Chart) ->
      (x : M) ->
      source chart x ->
      fromChart chart (toChart chart x) == x
    to-from-chart :
      (chart : Chart) ->
      (x : H) ->
      target chart x ->
      toChart chart (fromChart chart x) == x
    toChart-continuous :
      (chart : Chart) ->
      (U : Predicate H) ->
      Open topologyH U ->
      Open topologyM
        (\ x -> Both (source chart x) (U (toChart chart x)))
    fromChart-continuous :
      (chart : Chart) ->
      (U : Predicate M) ->
      Open topologyM U ->
      Open topologyH
        (\ x -> Both (target chart x) (U (fromChart chart x)))

open ChartedSpace

record LocalSmoothExtensionE
  {R E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedVectorSpace R E reals)
  (domain : Predicate E)
  (f : E -> E)
  (point : E) : Set1 where
  field
    local-extension :
      E -> E
    local-extension-smooth :
      SmoothFunctionE reals space local-extension
    local-extension-agrees :
      LocallyAgreeE space domain local-extension f point

SmoothOnCorner :
  {R E : Set}
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  Predicate E ->
  (E -> E) ->
  Set1
SmoothOnCorner space domain f =
  (point : _) ->
  domain point ->
  LocalSmoothExtensionE space domain f point

transitionDomain :
  {R E H M : Set}
  {reals : CompleteOrderedField R}
  {space : NormedVectorSpace R E reals}
  {topologyH : TopologicalSpace H}
  (model : ModelWithCorners reals space topologyH)
  {topologyM : TopologicalSpace M}
  (charts : ChartedSpace topologyH topologyM) ->
  Chart charts ->
  Chart charts ->
  Predicate E
transitionDomain model charts firstChart secondChart x =
  Both
    (carrier model x)
    (Both
      (target charts firstChart (fromModel model x))
      (source charts secondChart
        (fromChart charts firstChart (fromModel model x))))

transitionMap :
  {R E H M : Set}
  {reals : CompleteOrderedField R}
  {space : NormedVectorSpace R E reals}
  {topologyH : TopologicalSpace H}
  (model : ModelWithCorners reals space topologyH)
  {topologyM : TopologicalSpace M}
  (charts : ChartedSpace topologyH topologyM) ->
  Chart charts ->
  Chart charts ->
  E ->
  E
transitionMap model charts firstChart secondChart x =
  toModel model
    (toChart charts secondChart
      (fromChart charts firstChart (fromModel model x)))

record SmoothManifold
  {R E H M : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  {topologyH : TopologicalSpace H}
  (model : ModelWithCorners reals space topologyH)
  {topologyM : TopologicalSpace M}
  (charts : ChartedSpace topologyH topologyM) : Set2 where
  field
    smooth-transition :
      (firstChart secondChart : Chart charts) ->
      SmoothOnCorner space
        (transitionDomain model charts firstChart secondChart)
        (transitionMap model charts firstChart secondChart)

chartDomain :
  {R E H M : Set}
  {reals : CompleteOrderedField R}
  {space : NormedVectorSpace R E reals}
  {topologyH : TopologicalSpace H}
  (model : ModelWithCorners reals space topologyH)
  {topologyM : TopologicalSpace M}
  (charts : ChartedSpace topologyH topologyM) ->
  Chart charts ->
  Predicate E
chartDomain model charts chart x =
  Both
    (carrier model x)
    (target charts chart (fromModel model x))

record LocalSmoothRepresentative
  {R E H M : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  {topologyH : TopologicalSpace H}
  (model : ModelWithCorners reals space topologyH)
  {topologyM : TopologicalSpace M}
  (charts : ChartedSpace topologyH topologyM)
  {n : Nat}
  (f : M -> Vector R n)
  (point : M) : Set2 where
  field
    local-chart :
      Chart charts
    point-in-source :
      source charts local-chart point
    extension :
      E -> Vector R n
    smooth-extension :
      SmoothFunctionVector reals space extension
    agrees-in-chart :
      LocallyAgreeVector space
        (chartDomain model charts local-chart)
        extension
        (\ x ->
          f (fromChart charts local-chart (fromModel model x)))
        (toModel model (toChart charts local-chart point))

open LocalSmoothRepresentative

localDifferential :
  {R E H M : Set}
  {reals : CompleteOrderedField R}
  {space : NormedVectorSpace R E reals}
  {topologyH : TopologicalSpace H}
  {model : ModelWithCorners reals space topologyH}
  {topologyM : TopologicalSpace M}
  {charts : ChartedSpace topologyH topologyM}
  {n : Nat}
  {f : M -> Vector R n}
  {point : M} ->
  LocalSmoothRepresentative reals space model charts f point ->
  E ->
  Vector R n
localDifferential
  {model = model}
  {charts = charts}
  {point = point}
  representative =
  firstDerivativeVector
    (smooth-extension representative)
    (toModel model
      (toChart charts (local-chart representative) point))

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective f =
  (x y : _) ->
  f x == f y ->
  x == y

InjectiveVectorMap :
  {A R : Set}
  {n : Nat} ->
  (A -> Vector R n) ->
  Set
InjectiveVectorMap f =
  (x y : _) ->
  VectorEqual (f x) (f y) ->
  x == y

record SmoothImmersionAt
  {R E H M : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  {topologyH : TopologicalSpace H}
  (model : ModelWithCorners reals space topologyH)
  {topologyM : TopologicalSpace M}
  (charts : ChartedSpace topologyH topologyM)
  {n : Nat}
  (f : M -> Vector R n)
  (point : M) : Set2 where
  field
    representative :
      LocalSmoothRepresentative reals space model charts f point
    differential-injective :
      InjectiveVectorMap (localDifferential representative)

ContinuousToEuclidean :
  {R M : Set} ->
  (reals : CompleteOrderedField R) ->
  (topologyM : TopologicalSpace M) ->
  {n : Nat} ->
  (M -> Vector R n) ->
  Set1
ContinuousToEuclidean reals topologyM {n} f =
  (U : Predicate (Vector _ n)) ->
  VectorOpen reals n U ->
  Open topologyM (\ x -> U (f x))

record InducedOpenWitness
  {R M : Set}
  (reals : CompleteOrderedField R)
  {n : Nat}
  (f : M -> Vector R n)
  (U : Predicate M) : Set1 where
  field
    ambient-open-set :
      Predicate (Vector R n)
    ambient-is-open :
      VectorOpen reals n ambient-open-set
    preimage-characterization :
      (x : M) ->
      Iff (U x) (ambient-open-set (f x))

record InducesTopology
  {R M : Set}
  (reals : CompleteOrderedField R)
  (topologyM : TopologicalSpace M)
  {n : Nat}
  (f : M -> Vector R n) : Set2 where
  field
    open-has-ambient-witness :
      (U : Predicate M) ->
      Open topologyM U ->
      InducedOpenWitness reals f U
    ambient-witness-is-open :
      (U : Predicate M) ->
      InducedOpenWitness reals f U ->
      Open topologyM U

ClosedRange :
  {R M : Set} ->
  (reals : CompleteOrderedField R) ->
  {n : Nat} ->
  (M -> Vector R n) ->
  Set
ClosedRange {M = M} reals {n} f =
  VectorOpen reals n
    (\ y ->
      Not (Exists M (\ x -> VectorEqual (f x) y)))

record ClosedEmbedding
  {R M : Set}
  (reals : CompleteOrderedField R)
  (topologyM : TopologicalSpace M)
  {n : Nat}
  (f : M -> Vector R n) : Set2 where
  field
    embedding-injective :
      InjectiveVectorMap f
    embedding-continuous :
      ContinuousToEuclidean reals topologyM f
    embedding-induces-topology :
      InducesTopology reals topologyM f
    embedding-range-closed :
      ClosedRange reals f

record WhitneyEmbeddingExists
  {R E H M : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  {topologyH : TopologicalSpace H}
  (model : ModelWithCorners reals space topologyH)
  {topologyM : TopologicalSpace M}
  (charts : ChartedSpace topologyH topologyM) : Set2 where
  field
    euclidean-dimension :
      Nat
    embedding :
      M -> Vector R euclidean-dimension
    closed-embedding :
      ClosedEmbedding reals topologyM embedding
    smooth-with-injective-differential :
      (x : M) ->
      SmoothImmersionAt reals space model charts embedding x

whitney-embedding-theorem : Set2
whitney-embedding-theorem =
  (R E H M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (space : NormedVectorSpace R E reals) ->
  FiniteDimensional reals space ->
  (topologyH : TopologicalSpace H) ->
  (model : ModelWithCorners reals space topologyH) ->
  (topologyM : TopologicalSpace M) ->
  (charts : ChartedSpace topologyH topologyM) ->
  SmoothManifold reals space model charts ->
  Hausdorff topologyM ->
  Compact topologyM ->
  WhitneyEmbeddingExists reals space model charts
