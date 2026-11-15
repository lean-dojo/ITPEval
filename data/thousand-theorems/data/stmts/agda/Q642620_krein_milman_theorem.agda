-- Statement-only formalization of thousand-theorems corpus artifact Q642620,
-- "Krein–Milman theorem": every compact convex subset of a Hausdorff locally
-- convex real topological vector space is the closure of the convex hull of
-- its extreme points. This file contains no proof.

{-# OPTIONS --safe #-}

module Q642620_krein_milman_theorem where

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
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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
      (lessOrEqualR zeroR oneR) and (zeroR != oneR)

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

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  (lessOrEqualR reals x y) and (x != y)

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

Disjoint :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Subset X ->
  Set a
Disjoint {a} {X = X} U V =
  (x : X) ->
  U x ->
  V x ->
  Bottom {a}

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
          (StrictLess reals lower x)
          and
          ((StrictLess reals x upper)
          and
          ((y : R) ->
            StrictLess reals lower y ->
            StrictLess reals y upper ->
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
      (cover V) and (V x))

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
            (Member V selected) and (V x)))))

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

T2Space :
  {a : Level} ->
  {X : Set a} ->
  TopologicalSpace X ->
  Set (lsuc a)
T2Space {X = X} topology =
  (x y : X) ->
  x != y ->
  Exists (Subset X)
    (\ U ->
      Exists (Subset X)
        (\ V ->
          (IsOpen topology U)
          and
          ((IsOpen topology V)
          and
          ((U x)
          and
          ((V y)
          and
          Disjoint U V)))))

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
ContinuousAt {X = X} source target f x =
  (V : Subset _) ->
  IsOpen target V ->
  V (f x) ->
  Exists (Subset X)
    (\ U ->
      (IsOpen source U)
      and
      ((U x)
      and
      ((y : X) ->
        U y ->
        V (f y))))

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
  source-left source-right target f x y =
  (W : Subset _) ->
  IsOpen target W ->
  W (f x y) ->
  Exists (Subset X)
    (\ U ->
      Exists (Subset Y)
        (\ V ->
          (IsOpen source-left U)
          and
          ((IsOpen source-right V)
          and
          ((U x)
          and
          ((V y)
          and
          ((u : X) ->
            (v : Y) ->
            U u ->
            V v ->
            W (f u v)))))))

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
ContinuousScalarMultiplication {R = R} {E = E} space topologyR topologyE =
  (a : R) ->
  (x : E) ->
  ContinuousAt2 topologyR topologyE topologyE (scaleE space) a x

Convex :
  {e : Level}
  {R : Set}
  {E : Set e} ->
  (reals : CompleteOrderedField R) ->
  RealVectorSpace reals E ->
  Subset E ->
  Set e
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

LocallyConvexSpace :
  {e : Level}
  {R : Set}
  {E : Set e} ->
  (reals : CompleteOrderedField R) ->
  RealVectorSpace reals E ->
  TopologicalSpace E ->
  Set (lsuc e)
LocallyConvexSpace {E = E} reals space topology =
  (x : E) ->
  (U : Subset E) ->
  IsOpen topology U ->
  U x ->
  Exists (Subset E)
    (\ V ->
      (IsOpen topology V)
      and
      ((V x)
      and
      ((SubsetOf V U)
      and
      Convex reals space V)))

sumScalars :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumScalars reals {zero} coefficients =
  zeroR reals
sumScalars reals {suc n} coefficients =
  addR reals
    (coefficients fzero)
    (sumScalars reals (\ i -> coefficients (fsuc i)))

sumScaled :
  {e : Level}
  {R : Set}
  {E : Set e}
  {reals : CompleteOrderedField R} ->
  (space : RealVectorSpace reals E) ->
  {n : Nat} ->
  (Fin n -> R) ->
  (Fin n -> E) ->
  E
sumScaled space {zero} coefficients points =
  zeroE space
sumScaled space {suc n} coefficients points =
  addE space
    (scaleE space (coefficients fzero) (points fzero))
    (sumScaled space
      (\ i -> coefficients (fsuc i))
      (\ i -> points (fsuc i)))

ConvexCombination :
  {e : Level}
  {R : Set}
  {E : Set e} ->
  (reals : CompleteOrderedField R) ->
  (space : RealVectorSpace reals E) ->
  {n : Nat} ->
  (Fin n -> E) ->
  E ->
  Set e
ConvexCombination {R = R} reals space {n} points x =
  Exists (Fin n -> R)
    (\ coefficients ->
      (((i : Fin n) ->
        lessOrEqualR reals
          (zeroR reals)
          (coefficients i))
      and
      ((sumScalars reals coefficients == oneR reals)
      and
      (sumScaled space coefficients points == x))))

ConvexHull :
  {e : Level}
  {R : Set}
  {E : Set e} ->
  (reals : CompleteOrderedField R) ->
  (space : RealVectorSpace reals E) ->
  Subset E ->
  Subset E
ConvexHull {E = E} reals space S x =
  Exists Nat
    (\ n ->
      Exists (Fin n -> E)
        (\ points ->
          (((i : Fin n) ->
            S (points i))
          and
          ConvexCombination reals space points x)))

OpenSegment :
  {e : Level}
  {R : Set}
  {E : Set e} ->
  (reals : CompleteOrderedField R) ->
  (space : RealVectorSpace reals E) ->
  E ->
  E ->
  E ->
  Set e
OpenSegment {R = R} reals space x y z =
  Exists R
    (\ t ->
      (StrictLess reals (zeroR reals) t)
      and
      ((StrictLess reals t (oneR reals))
      and
      (z ==
        addE space
          (scaleE space t x)
          (scaleE space
            (subtractR reals (oneR reals) t)
            y))))

ExtremePoint :
  {e : Level}
  {R : Set}
  {E : Set e} ->
  (reals : CompleteOrderedField R) ->
  (space : RealVectorSpace reals E) ->
  Subset E ->
  E ->
  Set e
ExtremePoint {E = E} reals space S x =
  (S x)
  and
  ((y z : E) ->
    S y ->
    S z ->
    OpenSegment reals space y z x ->
    (y == x) and (z == x))

ExtremePoints :
  {e : Level}
  {R : Set}
  {E : Set e} ->
  (reals : CompleteOrderedField R) ->
  (space : RealVectorSpace reals E) ->
  Subset E ->
  Subset E
ExtremePoints reals space S =
  ExtremePoint reals space S

krein-milman-theorem : Setω
krein-milman-theorem =
  {e : Level} ->
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (topologyR : TopologicalSpace R) ->
  StandardRealTopology reals topologyR ->
  (E : Set e) ->
  (space : RealVectorSpace reals E) ->
  (topologyE : TopologicalSpace E) ->
  T2Space topologyE ->
  IsTopologicalAddGroup space topologyE ->
  ContinuousScalarMultiplication space topologyR topologyE ->
  LocallyConvexSpace reals space topologyE ->
  (S : Subset E) ->
  Compact topologyE S ->
  Convex reals space S ->
  SameSubset
    (close topologyE
      (ConvexHull reals space
        (ExtremePoints reals space S)))
    S
