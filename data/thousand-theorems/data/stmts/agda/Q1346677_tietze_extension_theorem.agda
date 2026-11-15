-- Statement-only formalization of thousand-theorems corpus artifact
-- thousand-theorems__agda__Q1346677, "Tietze extension theorem": every
-- bounded continuous real-valued function along a closed embedding into a
-- normal space has an extension with the same supremum norm. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Q1346677_tietze_extension_theorem where

open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} A =
  A -> Bottom {a}

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

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR absoluteR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) -> addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) -> addR x zeroR == x
    add-inverseR :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) -> multiplyR x oneR == x
    multiply-zeroR :
      (x : R) -> multiplyR x zeroR == zeroR
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
      (x : R) -> lessOrEqualR x x
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

    absolute-nonnegativeR :
      (x : R) -> lessOrEqualR zeroR (absoluteR x)
    absolute-of-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x
    absolute-of-nonpositiveR :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x
    absolute-zero-onlyR :
      (x : R) ->
      absoluteR x == zeroR ->
      x == zeroR
    absolute-negateR :
      (x : R) ->
      absoluteR (negateR x) == absoluteR x
    absolute-addR :
      (x y : R) ->
      lessOrEqualR (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y))
    absolute-multiplyR :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)

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

Predicate :
  {a q : Level} ->
  Set a ->
  Set (lsuc (a ⊔ q))
Predicate {a} {q} A =
  A -> Set (a ⊔ q)

Empty :
  {a q : Level} ->
  {A : Set a} ->
  Predicate {q = q} A
Empty {a} {q} _ =
  Bottom {a ⊔ q}

Union :
  {a q : Level} ->
  {A : Set a} ->
  Predicate {q = q} A ->
  Predicate {q = q} A ->
  Predicate {q = q} A
Union U V x =
  Either (U x) (V x)

Complement :
  {a q : Level} ->
  {A : Set a} ->
  Predicate {q = q} A ->
  Predicate {q = q} A
Complement U x =
  Not (U x)

SubsetOf :
  {a q : Level} ->
  {A : Set a} ->
  Predicate {q = q} A ->
  Predicate {q = q} A ->
  Set (a ⊔ q)
SubsetOf {A = A} U V =
  (x : A) ->
  U x ->
  V x

SameSubset :
  {a q : Level} ->
  {A : Set a} ->
  Predicate {q = q} A ->
  Predicate {q = q} A ->
  Set (a ⊔ q)
SameSubset {A = A} U V =
  (x : A) ->
  Iff (U x) (V x)

Disjoint :
  {a q : Level} ->
  {A : Set a} ->
  Predicate {q = q} A ->
  Predicate {q = q} A ->
  Set (a ⊔ q)
Disjoint {a} {q} {A} U V =
  (x : A) ->
  U x ->
  V x ->
  Bottom {a ⊔ q}

record TopologicalSpace
  {a q : Level}
  (X : Set a) :
  Set (lsuc (a ⊔ q)) where

  field
    close :
      Predicate {q = q} X ->
      Predicate {q = q} X

    close-congruent :
      (U V : Predicate {q = q} X) ->
      SameSubset {q = q} U V ->
      SameSubset {q = q} (close U) (close V)

    close-empty :
      SubsetOf {q = q}
        (close (Empty {q = q}))
        (Empty {q = q})

    subset-close :
      (U : Predicate {q = q} X) ->
      SubsetOf {q = q} U (close U)

    close-monotone :
      (U V : Predicate {q = q} X) ->
      SubsetOf {q = q} U V ->
      SubsetOf {q = q} (close U) (close V)

    close-union-forward :
      (U V : Predicate {q = q} X) ->
      SubsetOf {q = q}
        (close (Union {q = q} U V))
        (Union {q = q} (close U) (close V))

    close-union-backward :
      (U V : Predicate {q = q} X) ->
      SubsetOf {q = q}
        (Union {q = q} (close U) (close V))
        (close (Union {q = q} U V))

    close-idempotent :
      (U : Predicate {q = q} X) ->
      SubsetOf {q = q} (close (close U)) (close U)

open TopologicalSpace

IsClosed :
  {a q : Level} ->
  {X : Set a} ->
  TopologicalSpace {q = q} X ->
  Predicate {q = q} X ->
  Set (a ⊔ q)
IsClosed {q = q} topology C =
  SubsetOf {q = q} (close topology C) C

IsOpen :
  {a q : Level} ->
  {X : Set a} ->
  TopologicalSpace {q = q} X ->
  Predicate {q = q} X ->
  Set (a ⊔ q)
IsOpen {q = q} topology U =
  IsClosed {q = q} topology (Complement {q = q} U)

Continuous :
  {a b : Level} ->
  {X : Set a} ->
  {Y : Set b} ->
  TopologicalSpace {q = b} X ->
  TopologicalSpace {q = a} Y ->
  (X -> Y) ->
  Set (lsuc (a ⊔ b))
Continuous {a = a} {b = b} source target f =
  (U : Predicate {a = b} {q = a} _) ->
  IsOpen target U ->
  IsOpen source (\ x -> U (f x))

RealOpen :
  {q : Level} ->
  {R : Set} ->
  CompleteOrderedField R ->
  Predicate {q = q} R ->
  Set q
RealOpen {q} {R} reals U =
  (x : R) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : R) ->
          StrictLess reals
            (absoluteR reals (subtractR reals y x))
            radius ->
          U y))

ContinuousReal :
  {a q : Level} ->
  {X : Set a} ->
  {R : Set} ->
  CompleteOrderedField R ->
  TopologicalSpace {q = q} X ->
  (X -> R) ->
  Set (lsuc (a ⊔ q))
ContinuousReal {a = a} {q = q} reals topology f =
  (U : Predicate {q = a ⊔ q} _) ->
  RealOpen {q = a ⊔ q} reals U ->
  IsOpen topology (\ x -> U (f x))

record NormalSeparation
  {a q : Level}
  {Y : Set a}
  (topology : TopologicalSpace {q = q} Y)
  (C D : Predicate {q = q} Y) :
  Set (lsuc (a ⊔ q)) where

  field
    left-open-set :
      Predicate {q = q} Y
    right-open-set :
      Predicate {q = q} Y
    left-open :
      IsOpen {q = q} topology left-open-set
    right-open :
      IsOpen {q = q} topology right-open-set
    left-contained :
      SubsetOf {q = q} C left-open-set
    right-contained :
      SubsetOf {q = q} D right-open-set
    open-sets-disjoint :
      Disjoint {q = q} left-open-set right-open-set

NormalSpace :
  {a q : Level} ->
  {Y : Set a} ->
  TopologicalSpace {q = q} Y ->
  Set (lsuc (a ⊔ q))
NormalSpace {q = q} {Y = Y} topology =
  (C D : Predicate {q = q} Y) ->
  IsClosed {q = q} topology C ->
  IsClosed {q = q} topology D ->
  Disjoint {q = q} C D ->
  NormalSeparation {q = q} topology C D

record Lift
  {a p : Level}
  (A : Set a) :
  Set (a ⊔ p) where

  constructor lifted
  field
    lower : A

Range :
  {a b : Level} ->
  {X : Set a} ->
  {Y : Set b} ->
  (X -> Y) ->
  Predicate {q = a} Y
Range {a} {X = X} e y =
  Exists X (\ x -> Lift {p = a} (e x == y))

record InducedOpenWitness
  {a b : Level}
  {X : Set a}
  {Y : Set b}
  (target : TopologicalSpace {q = a} Y)
  (e : X -> Y)
  (U : Predicate {q = b} X) :
  Set (lsuc (a ⊔ b)) where

  field
    ambient-open-set :
      Predicate {q = a} Y
    ambient-is-open :
      IsOpen target ambient-open-set
    preimage-characterization :
      (x : X) ->
      Iff (U x) (ambient-open-set (e x))

record ClosedEmbedding
  {a b : Level}
  {X : Set a}
  {Y : Set b}
  (source : TopologicalSpace {q = b} X)
  (target : TopologicalSpace {q = a} Y)
  (e : X -> Y) :
  Set (lsuc (a ⊔ b)) where

  field
    embedding-injective :
      (x y : X) ->
      e x == e y ->
      x == y
    embedding-continuous :
      Continuous source target e
    embedding-induces-topology :
      (U : Predicate {q = b} X) ->
      IsOpen source U ->
      InducedOpenWitness target e U
    embedding-range-closed :
      IsClosed target (Range e)

record BoundedContinuous
  {a q : Level}
  {X : Set a}
  {R : Set}
  (reals : CompleteOrderedField R)
  (topology : TopologicalSpace {q = q} X) :
  Set (lsuc (a ⊔ q)) where

  field
    apply :
      X ->
      R
    apply-continuous :
      ContinuousReal reals topology apply
    norm :
      R
    norm-nonnegative :
      lessOrEqualR reals (zeroR reals) norm
    norm-upper :
      (x : X) ->
      lessOrEqualR reals (absoluteR reals (apply x)) norm
    norm-least :
      (upper : R) ->
      lessOrEqualR reals (zeroR reals) upper ->
      ((x : X) ->
        lessOrEqualR reals (absoluteR reals (apply x)) upper) ->
      lessOrEqualR reals norm upper

open BoundedContinuous

record NormPreservingExtension
  {a b : Level}
  {X : Set a}
  {Y : Set b}
  {R : Set}
  {reals : CompleteOrderedField R}
  {source : TopologicalSpace {q = b} X}
  {target : TopologicalSpace {q = a} Y}
  (f : BoundedContinuous reals source)
  (e : X -> Y) :
  Set (lsuc (a ⊔ b)) where

  field
    extension :
      BoundedContinuous reals target
    same-norm :
      norm extension == norm f
    extends :
      (x : X) ->
      apply extension (e x) == apply f x

tietze-extension-theorem : Setω
tietze-extension-theorem =
  (a b : Level) ->
  (R : Set) ->
  (X : Set a) ->
  (Y : Set b) ->
  (reals : CompleteOrderedField R) ->
  (source : TopologicalSpace {q = b} X) ->
  (target : TopologicalSpace {q = a} Y) ->
  NormalSpace target ->
  (f : BoundedContinuous reals source) ->
  (e : X -> Y) ->
  ClosedEmbedding source target e ->
  NormPreservingExtension {target = target} f e
