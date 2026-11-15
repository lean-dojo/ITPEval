-- Statement-only formalization of thousand-theorems corpus artifact Q7525341,
-- "Sion's minimax theorem": under compactness, convexity, semicontinuity, and
-- quasiconvexity/quasiconcavity hypotheses, the specified infimum of suprema
-- equals the specified supremum of infima. This file contains no proof.

{-# OPTIONS --safe #-}

module Q7525341_sion_s_minimax_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom {a : Level} : Set a where

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

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

record LogicalEquivalence
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor logically-equivalent
  field
    forward  : A -> B
    backward : B -> A

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

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

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
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
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
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
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
      lessOrEqualR x y or lessOrEqualR y x
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
      lessOrEqualR zeroR oneR and zeroR != oneR

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
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqualR x supremum)
          and
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
      LogicalEquivalence
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

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

StrictLessR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLessR reals x y =
  lessOrEqualR reals x y and x != y

Subset :
  {a : Level} ->
  Set a ->
  Set (lsuc a)
Subset {a} X =
  X -> Set a

Empty :
  {a : Level} ->
  {X : Set a} ->
  Subset X
Empty _ =
  Bottom

Union :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Subset X ->
  Subset X
Union U V x =
  U x or V x

Intersection :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Subset X ->
  Subset X
Intersection U V x =
  U x and V x

Complement :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Subset X
Complement U x =
  Not (U x)

SubsetOf :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Subset X ->
  Set a
SubsetOf {X = X} U V =
  (x : X) ->
  U x ->
  V x

SameSubset :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Subset X ->
  Set a
SameSubset {X = X} U V =
  (x : X) ->
  LogicalEquivalence (U x) (V x)

Family :
  {a : Level} ->
  Set a ->
  Set (lsuc (lsuc a))
Family {a} X =
  Subset X -> Set (lsuc a)

record TopologicalSpace
  {a : Level}
  (X : Set a) :
  Set (lsuc a) where

  field
    close :
      Subset X ->
      Subset X

    close-congruent :
      (U V : Subset X) ->
      SameSubset U V ->
      SameSubset (close U) (close V)

    close-empty :
      (x : X) ->
      close Empty x ->
      Bottom {a}

    subset-close :
      (U : Subset X) ->
      SubsetOf U (close U)

    close-monotone :
      (U V : Subset X) ->
      SubsetOf U V ->
      SubsetOf (close U) (close V)

    close-union-forward :
      (U V : Subset X) ->
      (x : X) ->
      close (Union U V) x ->
      close U x or close V x

    close-union-backward :
      (U V : Subset X) ->
      (x : X) ->
      (close U x or close V x) ->
      close (Union U V) x

    close-idempotent :
      (U : Subset X) ->
      SubsetOf (close (close U)) (close U)

open TopologicalSpace

IsClosed :
  {a : Level} ->
  {X : Set a} ->
  TopologicalSpace X ->
  Subset X ->
  Set a
IsClosed topology U =
  SubsetOf (close topology U) U

IsOpen :
  {a : Level} ->
  {X : Set a} ->
  TopologicalSpace X ->
  Subset X ->
  Set a
IsOpen topology U =
  IsClosed topology (Complement U)

OrderOpen :
  {R : Set} ->
  CompleteOrderedField R ->
  Subset R ->
  Set
OrderOpen {R = R} reals U =
  (x : R) ->
  U x ->
  Exists R
    (\ lower ->
      Exists R
        (\ upper ->
          StrictLessR reals lower x
          and
          (StrictLessR reals x upper
          and
          ((y : R) ->
            StrictLessR reals lower y ->
            StrictLessR reals y upper ->
            U y))))

StandardRealTopology :
  {R : Set} ->
  CompleteOrderedField R ->
  TopologicalSpace R ->
  Set1
StandardRealTopology reals topology =
  (U : Subset _) ->
  LogicalEquivalence
    (IsOpen topology U)
    (OrderOpen reals U)

Covers :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Family X ->
  Set (lsuc a)
Covers {X = X} U cover =
  (x : X) ->
  U x ->
  Σ (Subset X)
    (\ V ->
      cover V and V x)

FiniteSubcover :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Family X ->
  Set (lsuc a)
FiniteSubcover {X = X} U cover =
  Σ (List (Subset X))
    (\ selected ->
      (((V : Subset X) ->
        Member V selected ->
        cover V)
      and
      ((x : X) ->
        U x ->
        Σ (Subset X)
          (\ V ->
            Member V selected and V x))))

Compact :
  {a : Level} ->
  {X : Set a} ->
  TopologicalSpace X ->
  Subset X ->
  Set (lsuc (lsuc a))
Compact {X = X} topology U =
  (cover : Family X) ->
  ((V : Subset X) ->
    cover V ->
    IsOpen topology V) ->
  Covers U cover ->
  FiniteSubcover U cover

Nonempty :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Set a
Nonempty {X = X} U =
  Exists X U

record RealVectorSpace
  {e : Level}
  {R : Set}
  (reals : CompleteOrderedField R)
  (E : Set e) :
  Set (lsuc e) where

  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : R -> E -> E

    add-commutativeE :
      (x y : E) ->
      addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) ->
      addE x zeroE == x
    add-inverseE :
      (x : E) ->
      addE x (negateE x) == zeroE

    scale-oneE :
      (x : E) ->
      scaleE (oneR reals) x == x
    scale-associativeE :
      (a b : R) ->
      (x : E) ->
      scaleE (multiplyR reals a b) x ==
      scaleE a (scaleE b x)
    scale-add-vectorsE :
      (a : R) ->
      (x y : E) ->
      scaleE a (addE x y) ==
      addE (scaleE a x) (scaleE a y)
    scale-add-scalarsE :
      (a b : R) ->
      (x : E) ->
      scaleE (addR reals a b) x ==
      addE (scaleE a x) (scaleE b x)
    scale-zero-vectorE :
      (a : R) ->
      scaleE a zeroE == zeroE
    scale-zero-scalarE :
      (x : E) ->
      scaleE (zeroR reals) x == zeroE

open RealVectorSpace

ContinuousAt :
  {a b : Level}
  {X : Set a}
  {Y : Set b} ->
  TopologicalSpace X ->
  TopologicalSpace Y ->
  (X -> Y) ->
  X ->
  Set (lsuc a ⊔ lsuc b)
ContinuousAt {X = X} source target function x =
  (V : Subset _) ->
  IsOpen target V ->
  V (function x) ->
  Exists (Subset X)
    (\ U ->
      IsOpen source U
      and
      (U x
      and
      ((y : X) ->
        U y ->
        V (function y))))

ContinuousAt2 :
  {a b c : Level}
  {X : Set a}
  {Y : Set b}
  {Z : Set c} ->
  TopologicalSpace X ->
  TopologicalSpace Y ->
  TopologicalSpace Z ->
  (X -> Y -> Z) ->
  X ->
  Y ->
  Set (lsuc a ⊔ lsuc b ⊔ lsuc c)
ContinuousAt2 {X = X} {Y = Y}
  source-left source-right target function x y =
  (W : Subset _) ->
  IsOpen target W ->
  W (function x y) ->
  Exists (Subset X)
    (\ U ->
      Exists (Subset Y)
        (\ V ->
          IsOpen source-left U
          and
          (IsOpen source-right V
          and
          (U x
          and
          (V y
          and
          ((u : X) ->
            (v : Y) ->
            U u ->
            V v ->
            W (function u v)))))))

IsTopologicalAddGroup :
  {e : Level}
  {R : Set}
  {E : Set e}
  {reals : CompleteOrderedField R} ->
  RealVectorSpace reals E ->
  TopologicalSpace E ->
  Set (lsuc e)
IsTopologicalAddGroup {E = E} space topology =
  (((x y : E) ->
    ContinuousAt2 topology topology topology (addE space) x y)
  and
  ((x : E) ->
    ContinuousAt topology topology (negateE space) x))

ContinuousScalarMultiplication :
  {e : Level}
  {R : Set}
  {E : Set e}
  {reals : CompleteOrderedField R} ->
  RealVectorSpace reals E ->
  TopologicalSpace R ->
  TopologicalSpace E ->
  Set (lsuc e)
ContinuousScalarMultiplication {R = R} {E = E}
  space topologyR topologyE =
  (a : R) ->
  (x : E) ->
  ContinuousAt2 topologyR topologyE topologyE (scaleE space) a x

Convex :
  {e p : Level}
  {R : Set}
  {E : Set e} ->
  (reals : CompleteOrderedField R) ->
  RealVectorSpace reals E ->
  (E -> Set p) ->
  Set (e ⊔ p)
Convex {R = R} {E = E} reals space S =
  (x y : E) ->
  S x ->
  S y ->
  (t : R) ->
  lessOrEqualR reals (zeroR reals) t ->
  lessOrEqualR reals t (oneR reals) ->
  S
    (addE space
      (scaleE space t x)
      (scaleE space
        (subtractR reals (oneR reals) t)
        y))

record DenselyOrderedLinearOrder
  {b : Level}
  (B : Set b) :
  Set (lsuc b) where

  field
    lessOrEqualB :
      B ->
      B ->
      Set b

    order-reflexiveB :
      (x : B) ->
      lessOrEqualB x x
    order-transitiveB :
      (x y z : B) ->
      lessOrEqualB x y ->
      lessOrEqualB y z ->
      lessOrEqualB x z
    order-antisymmetricB :
      (x y : B) ->
      lessOrEqualB x y ->
      lessOrEqualB y x ->
      x == y
    order-totalB :
      (x y : B) ->
      lessOrEqualB x y or lessOrEqualB y x

    densely-orderedB :
      (x y : B) ->
      (lessOrEqualB x y and x != y) ->
      Exists B
        (\ z ->
          (lessOrEqualB x z and x != z)
          and
          (lessOrEqualB z y and z != y))

open DenselyOrderedLinearOrder

StrictLessB :
  {b : Level}
  {B : Set b} ->
  DenselyOrderedLinearOrder B ->
  B ->
  B ->
  Set b
StrictLessB order x y =
  lessOrEqualB order x y and x != y

LowerSemicontinuousOn :
  {e b : Level}
  {E : Set e}
  {B : Set b} ->
  TopologicalSpace E ->
  DenselyOrderedLinearOrder B ->
  (E -> B) ->
  Subset E ->
  Set (lsuc e ⊔ b)
LowerSemicontinuousOn {E = E} topology order function domain =
  (x : E) ->
  domain x ->
  (threshold : _) ->
  StrictLessB order threshold (function x) ->
  Exists (Subset E)
    (\ U ->
      IsOpen topology U
      and
      (U x
      and
      ((x' : E) ->
        domain x' ->
        U x' ->
        StrictLessB order threshold (function x'))))

UpperSemicontinuousOn :
  {e b : Level}
  {E : Set e}
  {B : Set b} ->
  TopologicalSpace E ->
  DenselyOrderedLinearOrder B ->
  (E -> B) ->
  Subset E ->
  Set (lsuc e ⊔ b)
UpperSemicontinuousOn {E = E} topology order function domain =
  (x : E) ->
  domain x ->
  (threshold : _) ->
  StrictLessB order (function x) threshold ->
  Exists (Subset E)
    (\ U ->
      IsOpen topology U
      and
      (U x
      and
      ((x' : E) ->
        domain x' ->
        U x' ->
        StrictLessB order (function x') threshold)))

Sublevel :
  {e b : Level}
  {E : Set e}
  {B : Set b} ->
  DenselyOrderedLinearOrder B ->
  Subset E ->
  (E -> B) ->
  B ->
  E ->
  Set (e ⊔ b)
Sublevel order domain function threshold x =
  domain x and lessOrEqualB order (function x) threshold

Superlevel :
  {e b : Level}
  {E : Set e}
  {B : Set b} ->
  DenselyOrderedLinearOrder B ->
  Subset E ->
  (E -> B) ->
  B ->
  E ->
  Set (e ⊔ b)
Superlevel order domain function threshold x =
  domain x and lessOrEqualB order threshold (function x)

QuasiconvexOn :
  {e b : Level}
  {R : Set}
  {E : Set e}
  {B : Set b}
  {reals : CompleteOrderedField R} ->
  RealVectorSpace reals E ->
  DenselyOrderedLinearOrder B ->
  Subset E ->
  (E -> B) ->
  Set (e ⊔ b)
QuasiconvexOn {reals = reals} space order domain function =
  (threshold : _) ->
  Convex reals space (Sublevel order domain function threshold)

QuasiconcaveOn :
  {e b : Level}
  {R : Set}
  {E : Set e}
  {B : Set b}
  {reals : CompleteOrderedField R} ->
  RealVectorSpace reals E ->
  DenselyOrderedLinearOrder B ->
  Subset E ->
  (E -> B) ->
  Set (e ⊔ b)
QuasiconcaveOn {reals = reals} space order domain function =
  (threshold : _) ->
  Convex reals space (Superlevel order domain function threshold)

ImageValues :
  {a b : Level}
  {A : Set a}
  {B : Set b} ->
  Subset A ->
  (A -> B) ->
  B ->
  Set (a ⊔ b)
ImageValues {A = A} subset function value =
  Exists A
    (\ x ->
      subset x and function x == value)

IsLeastUpperBound :
  {b p : Level}
  {B : Set b} ->
  DenselyOrderedLinearOrder B ->
  (B -> Set p) ->
  B ->
  Set (b ⊔ p)
IsLeastUpperBound {B = B} order candidates bound =
  (((x : B) ->
    candidates x ->
    lessOrEqualB order x bound)
  and
  ((upper : B) ->
    ((x : B) ->
      candidates x ->
      lessOrEqualB order x upper) ->
    lessOrEqualB order bound upper))

IsGreatestLowerBound :
  {b p : Level}
  {B : Set b} ->
  DenselyOrderedLinearOrder B ->
  (B -> Set p) ->
  B ->
  Set (b ⊔ p)
IsGreatestLowerBound {B = B} order candidates bound =
  (((x : B) ->
    candidates x ->
    lessOrEqualB order bound x)
  and
  ((lower : B) ->
    ((x : B) ->
      candidates x ->
      lessOrEqualB order lower x) ->
    lessOrEqualB order lower bound))

sion-s-minimax-theorem : Setω
sion-s-minimax-theorem =
  {e f b : Level} ->
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (topologyR : TopologicalSpace R) ->
  StandardRealTopology reals topologyR ->
  (E : Set e) ->
  (spaceE : RealVectorSpace reals E) ->
  (topologyE : TopologicalSpace E) ->
  IsTopologicalAddGroup spaceE topologyE ->
  ContinuousScalarMultiplication spaceE topologyR topologyE ->
  (F : Set f) ->
  (spaceF : RealVectorSpace reals F) ->
  (topologyF : TopologicalSpace F) ->
  IsTopologicalAddGroup spaceF topologyF ->
  ContinuousScalarMultiplication spaceF topologyR topologyF ->
  (B : Set b) ->
  (orderB : DenselyOrderedLinearOrder B) ->
  (X : Subset E) ->
  Nonempty X ->
  Compact topologyE X ->
  Convex reals spaceE X ->
  (Y : Subset F) ->
  Convex reals spaceF Y ->
  (payoff : E -> F -> B) ->
  ((y : F) ->
    Y y ->
    LowerSemicontinuousOn
      topologyE orderB (\ x -> payoff x y) X) ->
  ((y : F) ->
    Y y ->
    QuasiconvexOn
      spaceE orderB X (\ x -> payoff x y)) ->
  ((x : E) ->
    X x ->
    UpperSemicontinuousOn
      topologyF orderB (payoff x) Y) ->
  ((x : E) ->
    X x ->
    QuasiconcaveOn
      spaceF orderB Y (payoff x)) ->
  (supremum-over-Y : E -> B) ->
  ((x : E) ->
    X x ->
    IsLeastUpperBound orderB
      (ImageValues Y (payoff x))
      (supremum-over-Y x)) ->
  (infimum-of-suprema : B) ->
  IsGreatestLowerBound orderB
    (ImageValues X supremum-over-Y)
    infimum-of-suprema ->
  (infimum-over-X : F -> B) ->
  ((y : F) ->
    Y y ->
    IsGreatestLowerBound orderB
      (ImageValues X (\ x -> payoff x y))
      (infimum-over-X y)) ->
  (supremum-of-infima : B) ->
  IsLeastUpperBound orderB
    (ImageValues Y infimum-over-X)
    supremum-of-infima ->
  infimum-of-suprema == supremum-of-infima
