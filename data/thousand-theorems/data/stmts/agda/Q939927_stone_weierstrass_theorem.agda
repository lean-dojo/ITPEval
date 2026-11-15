-- Statement-only formalization of thousand-theorems corpus artifact
-- thousand-theorems__agda__Q939927, "Stone–Weierstrass theorem": a real
-- subalgebra of continuous functions on a compact topological space is
-- uniformly dense when it separates points. This file contains no proof.

{-# OPTIONS --safe #-}

module Q939927_stone_weierstrass_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

-- A complete Archimedean ordered field is a presentation of the real line.
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

    negateR reciprocalR absoluteR :
      R ->
      R

    lessOrEqualR :
      R ->
      R ->
      Set r

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
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)

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

    order-reflexive :
      (x : R) ->
      lessOrEqualR x x

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
      Exists Nat
        (\ n ->
          lessOrEqualR x (fromNatR n))

    least-upper-bound :
      (P : R -> Set r) ->
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

open RealLine

record RealLineEquivalence
  {r : Level}
  {R S : Set r}
  (source : RealLine R)
  (target : RealLine S) :
  Set (lsuc r) where

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

    forward-absoluteR :
      (x : R) ->
      forwardR (absoluteR source x) ==
      absoluteR target (forwardR x)

    forward-fromNatR :
      (n : Nat) ->
      forwardR (fromNatR source n) ==
      fromNatR target n

    forward-orderR :
      (x y : R) ->
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {r : Level}
  {R : Set r}
  (reals : RealLine R) :
  Set (lsuc r) where

  field
    equivalent-real-line :
      (S : Set r) ->
      (other : RealLine S) ->
      RealLineEquivalence reals other

subtractR :
  {r : Level} ->
  {R : Set r} ->
  RealLine R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

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

Subset :
  {a p : Level} ->
  Set a ->
  Set (a ⊔ lsuc p)
Subset {p = p} X =
  X -> Set p

Empty :
  {a p : Level} ->
  {X : Set a} ->
  Subset {p = p} X
Empty {p = p} _ =
  Bottom {p}

Whole :
  {a p : Level} ->
  {X : Set a} ->
  Subset {p = p} X
Whole {p = p} _ =
  Top {p}

Union :
  {a p : Level} ->
  {X : Set a} ->
  Subset {p = p} X ->
  Subset {p = p} X ->
  Subset {p = p} X
Union U V x =
  Either (U x) (V x)

Complement :
  {a p : Level} ->
  {X : Set a} ->
  Subset {p = p} X ->
  Subset {p = p} X
Complement U x =
  Not (U x)

SubsetOf :
  {a p : Level} ->
  {X : Set a} ->
  Subset {p = p} X ->
  Subset {p = p} X ->
  Set (a ⊔ p)
SubsetOf {X = X} U V =
  (x : X) ->
  U x ->
  V x

SameSubset :
  {a p : Level} ->
  {X : Set a} ->
  Subset {p = p} X ->
  Subset {p = p} X ->
  Set (a ⊔ p)
SameSubset {X = X} U V =
  (x : X) ->
  Iff (U x) (V x)

Family :
  {a p : Level} ->
  Set a ->
  Set (a ⊔ lsuc p)
Family {p = p} X =
  Subset {p = p} X -> Set p

record TopologicalSpace
  {a p : Level}
  (X : Set a) :
  Set (lsuc (a ⊔ p)) where

  field
    close :
      Subset {p = p} X ->
      Subset {p = p} X

    close-congruent :
      (U V : Subset {p = p} X) ->
      SameSubset U V ->
      SameSubset (close U) (close V)

    close-empty :
      SubsetOf (close Empty) Empty

    subset-close :
      (U : Subset {p = p} X) ->
      SubsetOf U (close U)

    close-monotone :
      (U V : Subset {p = p} X) ->
      SubsetOf U V ->
      SubsetOf (close U) (close V)

    close-union-forward :
      (U V : Subset {p = p} X) ->
      SubsetOf
        (close (Union U V))
        (Union (close U) (close V))

    close-union-backward :
      (U V : Subset {p = p} X) ->
      SubsetOf
        (Union (close U) (close V))
        (close (Union U V))

    close-idempotent :
      (U : Subset {p = p} X) ->
      SubsetOf (close (close U)) (close U)

open TopologicalSpace

IsClosed :
  {a p : Level} ->
  {X : Set a} ->
  TopologicalSpace {p = p} X ->
  Subset {p = p} X ->
  Set (a ⊔ p)
IsClosed topology U =
  SubsetOf (close topology U) U

IsOpen :
  {a p : Level} ->
  {X : Set a} ->
  TopologicalSpace {p = p} X ->
  Subset {p = p} X ->
  Set (a ⊔ p)
IsOpen topology U =
  IsClosed topology (Complement U)

Covers :
  {a p : Level} ->
  {X : Set a} ->
  Subset {p = p} X ->
  Family {p = p} X ->
  Set (a ⊔ lsuc p)
Covers {p = p} {X = X} U cover =
  (x : X) ->
  U x ->
  Exists (Subset {p = p} X)
    (\ V ->
      Both
        (cover V)
        (V x))

FiniteSubcover :
  {a p : Level} ->
  {X : Set a} ->
  Subset {p = p} X ->
  Family {p = p} X ->
  Set (a ⊔ lsuc p)
FiniteSubcover {p = p} {X = X} U cover =
  Exists (List (Subset {p = p} X))
    (\ selected ->
      Both
        ((V : Subset {p = p} X) ->
          Member V selected ->
          cover V)
        ((x : X) ->
          U x ->
          Exists (Subset {p = p} X)
            (\ V ->
              Both
                (Member V selected)
                (V x))))

Compact :
  {a p : Level} ->
  {X : Set a} ->
  TopologicalSpace {p = p} X ->
  Subset {p = p} X ->
  Set (a ⊔ lsuc p)
Compact {p = p} {X = X} topology U =
  (cover : Family {p = p} X) ->
  ((V : Subset {p = p} X) ->
    cover V ->
    IsOpen topology V) ->
  Covers U cover ->
  FiniteSubcover U cover

OrderOpen :
  {r : Level} ->
  {R : Set r} ->
  RealLine R ->
  Subset {p = r} R ->
  Set r
OrderOpen {R = R} reals U =
  (x : R) ->
  U x ->
  Exists R
    (\ lower ->
      Exists R
        (\ upper ->
          Both
            (StrictLess reals lower x)
            (Both
              (StrictLess reals x upper)
              ((y : R) ->
                StrictLess reals lower y ->
                StrictLess reals y upper ->
                U y))))

ContinuousReal :
  {r x : Level} ->
  {R : Set r} ->
  {X : Set x} ->
  RealLine R ->
  TopologicalSpace {p = r} X ->
  (X -> R) ->
  Set (lsuc r ⊔ x)
ContinuousReal {r} {R = R} reals topology function =
  (U : Subset {p = r} R) ->
  OrderOpen reals U ->
  IsOpen topology
    (\ x ->
      U (function x))

record RealSubalgebra
  {r x : Level}
  {R : Set r}
  {X : Set x}
  (reals : RealLine R)
  (topology : TopologicalSpace {p = r} X) :
  Set (lsuc (r ⊔ x)) where

  field
    contains :
      (X -> R) ->
      Set (r ⊔ x)

    member-congruent :
      (f g : X -> R) ->
      ((point : X) ->
        f point == g point) ->
      contains f ->
      contains g

    member-continuous :
      (f : X -> R) ->
      contains f ->
      ContinuousReal reals topology f

    constant-member :
      (constant : R) ->
      contains
        (\ _ ->
          constant)

    add-member :
      (f g : X -> R) ->
      contains f ->
      contains g ->
      contains
        (\ point ->
          addR reals (f point) (g point))

    negate-member :
      (f : X -> R) ->
      contains f ->
      contains
        (\ point ->
          negateR reals (f point))

    multiply-member :
      (f g : X -> R) ->
      contains f ->
      contains g ->
      contains
        (\ point ->
          multiplyR reals (f point) (g point))

open RealSubalgebra

SeparatesPoints :
  {r x : Level} ->
  {R : Set r} ->
  {X : Set x} ->
  {reals : RealLine R} ->
  {topology : TopologicalSpace {p = r} X} ->
  RealSubalgebra reals topology ->
  Set (r ⊔ x)
SeparatesPoints {R = R} {X = X} algebra =
  (leftPoint rightPoint : X) ->
  leftPoint != rightPoint ->
  Exists (X -> R)
    (\ function ->
      Both
        (contains algebra function)
        (function leftPoint != function rightPoint))

UniformlyClose :
  {r x : Level} ->
  {R : Set r} ->
  {X : Set x} ->
  (reals : RealLine R) ->
  R ->
  (X -> R) ->
  (X -> R) ->
  Set (r ⊔ x)
UniformlyClose {X = X} reals epsilon f g =
  (point : X) ->
  StrictLess reals
    (absoluteR reals
      (subtractR reals (g point) (f point)))
    epsilon

InUniformClosure :
  {r x : Level} ->
  {R : Set r} ->
  {X : Set x} ->
  {reals : RealLine R} ->
  {topology : TopologicalSpace {p = r} X} ->
  RealSubalgebra reals topology ->
  (X -> R) ->
  Set (r ⊔ x)
InUniformClosure {R = R} {X = X} {reals = reals} algebra f =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists (X -> R)
    (\ g ->
      Both
        (contains algebra g)
        (UniformlyClose reals epsilon f g))

stone-weierstrass-theorem :
  {r x : Level} ->
  Set (lsuc (r ⊔ x))
stone-weierstrass-theorem {r} {x} =
  (R : Set r) ->
  (reals : RealLine R) ->
  RealNumberPresentation reals ->
  (X : Set x) ->
  (topology : TopologicalSpace {p = r} X) ->
  Compact topology Whole ->
  (algebra : RealSubalgebra reals topology) ->
  SeparatesPoints algebra ->
  (function : X -> R) ->
  ContinuousReal reals topology function ->
  InUniformClosure algebra function
