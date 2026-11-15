-- Statement-only formalization of thousand-theorems corpus artifact Q5638886,
-- "Hahn embedding theorem": every linearly ordered abelian group has an
-- injective order-preserving additive embedding into the lexicographically
-- ordered group of real Hahn series indexed by its nonzero finite
-- Archimedean classes, with each nonzero element's class equal to the leading
-- index of its image. This file contains no proof.

{-# OPTIONS --safe #-}

module Q5638886_hahn_embedding_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat) renaming (zero to zeroN; suc to sucN)

infix 4 _≠_
infixr 3 _×_

data Bottom {a : Level} : Set a where

data Top {a : Level} : Set a where
  inhabitant : Top

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} proposition =
  proposition -> Bottom {a}

_≠_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x ≠ y =
  Not (x ≡ y)

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record Exists
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

  constructor witness
  field
    value    : A
    property : P value

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

record OrderedAbelianGroup
  {a : Level}
  (M : Set a) :
  Set (lsuc a) where

  field
    zeroM :
      M

    addM :
      M ->
      M ->
      M

    negateM :
      M ->
      M

    lessOrEqualM :
      M ->
      M ->
      Set a

    absoluteValueM :
      M ->
      M

    add-associativeM :
      (x y z : M) ->
      addM (addM x y) z ≡ addM x (addM y z)

    add-commutativeM :
      (x y : M) ->
      addM x y ≡ addM y x

    add-zeroM :
      (x : M) ->
      addM x zeroM ≡ x

    add-inverseM :
      (x : M) ->
      addM x (negateM x) ≡ zeroM

    order-propositionalM :
      (x y : M) ->
      (p q : lessOrEqualM x y) ->
      p ≡ q

    order-reflexiveM :
      (x : M) ->
      lessOrEqualM x x

    order-transitiveM :
      (x y z : M) ->
      lessOrEqualM x y ->
      lessOrEqualM y z ->
      lessOrEqualM x z

    order-antisymmetricM :
      (x y : M) ->
      lessOrEqualM x y ->
      lessOrEqualM y x ->
      x ≡ y

    order-totalM :
      (x y : M) ->
      Either (lessOrEqualM x y) (lessOrEqualM y x)

    add-orderM :
      (x y z : M) ->
      lessOrEqualM x y ->
      lessOrEqualM (addM z x) (addM z y)

    absolute-upper-positiveM :
      (x : M) ->
      lessOrEqualM x (absoluteValueM x)

    absolute-upper-negativeM :
      (x : M) ->
      lessOrEqualM (negateM x) (absoluteValueM x)

    absolute-choiceM :
      (x : M) ->
      Either
        (absoluteValueM x ≡ x)
        (absoluteValueM x ≡ negateM x)

open OrderedAbelianGroup

naturalMultiple :
  {a : Level} ->
  {M : Set a} ->
  OrderedAbelianGroup M ->
  Nat ->
  M ->
  M
naturalMultiple group zeroN x =
  zeroM group
naturalMultiple group (sucN n) x =
  addM group x (naturalMultiple group n x)

ArchimedeanClassLessOrEqual :
  {a : Level} ->
  {M : Set a} ->
  OrderedAbelianGroup M ->
  M ->
  M ->
  Set a
ArchimedeanClassLessOrEqual group x y =
  Exists Nat
    (\ n ->
      lessOrEqualM group
        (absoluteValueM group y)
        (naturalMultiple group n (absoluteValueM group x)))

ArchimedeanEquivalent :
  {a : Level} ->
  {M : Set a} ->
  OrderedAbelianGroup M ->
  M ->
  M ->
  Set a
ArchimedeanEquivalent group x y =
  ArchimedeanClassLessOrEqual group x y
  ×
  ArchimedeanClassLessOrEqual group y x

-- This is an exact quotient presentation of the nonzero finite
-- Archimedean classes.  The order criterion has the same orientation as
-- FiniteArchimedeanClass: [x] <= [y] iff |y| <= n |x| for some natural n.
record FiniteArchimedeanClasses
  {a c : Level}
  {M : Set a}
  (group : OrderedAbelianGroup M)
  (Class : Set c) :
  Set (lsuc (a ⊔ c)) where

  field
    classOf :
      (x : M) ->
      x ≠ zeroM group ->
      Class

    classLessOrEqual :
      Class ->
      Class ->
      Set (a ⊔ c)

    class-order-propositional :
      (x y : Class) ->
      (p q : classLessOrEqual x y) ->
      p ≡ q

    class-order-reflexive :
      (x : Class) ->
      classLessOrEqual x x

    class-order-transitive :
      (x y z : Class) ->
      classLessOrEqual x y ->
      classLessOrEqual y z ->
      classLessOrEqual x z

    class-order-antisymmetric :
      (x y : Class) ->
      classLessOrEqual x y ->
      classLessOrEqual y x ->
      x ≡ y

    class-order-total :
      (x y : Class) ->
      Either
        (classLessOrEqual x y)
        (classLessOrEqual y x)

    classOf-proof-independent :
      (x : M) ->
      (p q : x ≠ zeroM group) ->
      classOf x p ≡ classOf x q

    classOf-equality :
      (x y : M) ->
      (x-nonzero : x ≠ zeroM group) ->
      (y-nonzero : y ≠ zeroM group) ->
      Iff
        (classOf x x-nonzero ≡ classOf y y-nonzero)
        (ArchimedeanEquivalent group x y)

    classOf-order :
      (x y : M) ->
      (x-nonzero : x ≠ zeroM group) ->
      (y-nonzero : y ≠ zeroM group) ->
      Iff
        (classLessOrEqual
          (classOf x x-nonzero)
          (classOf y y-nonzero))
        (ArchimedeanClassLessOrEqual group x y)

    representative :
      Class ->
      M

    representative-nonzero :
      (class : Class) ->
      representative class ≠ zeroM group

    representative-class :
      (class : Class) ->
      classOf
        (representative class)
        (representative-nonzero class)
      ≡ class

open FiniteArchimedeanClasses

Subset :
  {a : Level} ->
  Set a ->
  Set (lsuc a)
Subset {a} X =
  X -> Set a

-- A complete Archimedean ordered field is a presentation of the real line.
record RealLine
  {a : Level}
  (R : Set a) :
  Set (lsuc a) where

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
      Set a

    fromNatR :
      Nat ->
      R

    one-not-zeroR :
      oneR ≠ zeroR

    add-commutativeR :
      (x y : R) ->
      addR x y ≡ addR y x

    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z ≡ addR x (addR y z)

    add-zeroR :
      (x : R) ->
      addR x zeroR ≡ x

    add-inverseR :
      (x : R) ->
      addR x (negateR x) ≡ zeroR

    multiply-commutativeR :
      (x y : R) ->
      multiplyR x y ≡ multiplyR y x

    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ≡ multiplyR x (multiplyR y z)

    multiply-oneR :
      (x : R) ->
      multiplyR x oneR ≡ x

    multiply-zeroR :
      (x : R) ->
      multiplyR x zeroR ≡ zeroR

    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)

    reciprocal-zeroR :
      reciprocalR zeroR ≡ zeroR

    multiply-reciprocalR :
      (x : R) ->
      x ≠ zeroR ->
      multiplyR x (reciprocalR x) ≡ oneR

    order-propositionalR :
      (x y : R) ->
      (p q : lessOrEqualR x y) ->
      p ≡ q

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
      x ≡ y

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
      lessOrEqualR zeroR oneR × zeroR ≠ oneR

    fromNat-zeroR :
      fromNatR zeroN ≡ zeroR

    fromNat-successorR :
      (n : Nat) ->
      fromNatR (sucN n) ≡ addR (fromNatR n) oneR

    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m ≡ fromNatR n ->
      m ≡ n

    archimedeanR :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqualR x (fromNatR n))

    least-upper-boundR :
      (P : R -> Set a) ->
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
          ×
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

open RealLine

StrictLess :
  {a : Level} ->
  {A : Set a} ->
  (A -> A -> Set a) ->
  A ->
  A ->
  Set a
StrictLess lessOrEqual x y =
  lessOrEqual x y × x ≠ y

ClassStrictLess :
  {a c : Level} ->
  {M : Set a} ->
  {Class : Set c} ->
  {group : OrderedAbelianGroup M} ->
  FiniteArchimedeanClasses group Class ->
  Class ->
  Class ->
  Set (a ⊔ c)
ClassStrictLess classes x y =
  classLessOrEqual classes x y × x ≠ y

data AccessibleOn
  {c q s : Level}
  {Class : Set c}
  (less : Class -> Class -> Set q)
  (support : Class -> Set s)
  (x : Class) :
  Set (c ⊔ q ⊔ s) where

  accessible :
    ((y : Class) ->
      support y ->
      less y x ->
      AccessibleOn less support y) ->
    AccessibleOn less support x

WellFoundedOn :
  {c q s : Level} ->
  {Class : Set c} ->
  (Class -> Class -> Set q) ->
  (Class -> Set s) ->
  Set (c ⊔ q ⊔ s)
WellFoundedOn {Class = Class} less support =
  (x : Class) ->
  support x ->
  AccessibleOn less support x

record HahnSeries
  {a c r : Level}
  {M : Set a}
  {Class : Set c}
  {R : Set r}
  {group : OrderedAbelianGroup M}
  (classes : FiniteArchimedeanClasses group Class)
  (reals : RealLine R) :
  Set (a ⊔ c ⊔ r) where

  field
    coefficient :
      Class ->
      R

    support-well-founded :
      WellFoundedOn
        (ClassStrictLess classes)
        (\ class -> coefficient class ≠ zeroR reals)

open HahnSeries

SeriesEqual :
  {a c r : Level}
  {M : Set a}
  {Class : Set c}
  {R : Set r}
  {group : OrderedAbelianGroup M}
  {classes : FiniteArchimedeanClasses group Class}
  {reals : RealLine R} ->
  HahnSeries classes reals ->
  HahnSeries classes reals ->
  Set (c ⊔ r)
SeriesEqual {Class = Class} x y =
  (class : Class) ->
  coefficient x class ≡ coefficient y class

LexicographicallyLess :
  {a c r : Level}
  {M : Set a}
  {Class : Set c}
  {R : Set r}
  {group : OrderedAbelianGroup M}
  (classes : FiniteArchimedeanClasses group Class)
  (reals : RealLine R) ->
  HahnSeries classes reals ->
  HahnSeries classes reals ->
  Set (a ⊔ c ⊔ r)
LexicographicallyLess {Class = Class} classes reals x y =
  Exists Class
    (\ leading ->
      (((earlier : Class) ->
        ClassStrictLess classes earlier leading ->
        coefficient x earlier ≡ coefficient y earlier)
      ×
      StrictLess
        (lessOrEqualR reals)
        (coefficient x leading)
        (coefficient y leading)))

LexicographicallyLessOrEqual :
  {a c r : Level}
  {M : Set a}
  {Class : Set c}
  {R : Set r}
  {group : OrderedAbelianGroup M}
  (classes : FiniteArchimedeanClasses group Class)
  (reals : RealLine R) ->
  HahnSeries classes reals ->
  HahnSeries classes reals ->
  Set (a ⊔ c ⊔ r)
LexicographicallyLessOrEqual classes reals x y =
  Either
    (SeriesEqual x y)
    (LexicographicallyLess classes reals x y)

data WithTop
  {c : Level}
  (Class : Set c) :
  Set c where

  finite : Class -> WithTop Class
  top    : WithTop Class

LeadingIndex :
  {a c r : Level}
  {M : Set a}
  {Class : Set c}
  {R : Set r}
  {group : OrderedAbelianGroup M}
  (classes : FiniteArchimedeanClasses group Class)
  (reals : RealLine R) ->
  HahnSeries classes reals ->
  WithTop Class ->
  Set (a ⊔ c ⊔ r)
LeadingIndex {Class = Class} classes reals series (finite leading) =
  (coefficient series leading ≠ zeroR reals)
  ×
  ((class : Class) ->
    coefficient series class ≠ zeroR reals ->
    classLessOrEqual classes leading class)
LeadingIndex {a = a} {Class = Class} classes reals series top =
  ((class : Class) ->
    coefficient series class ≡ zeroR reals)
  ×
  Top {a}

SourceClass :
  {a c : Level}
  {M : Set a}
  {Class : Set c}
  {group : OrderedAbelianGroup M}
  (classes : FiniteArchimedeanClasses group Class) ->
  M ->
  WithTop Class ->
  Set (a ⊔ c)
SourceClass {group = group} classes x (finite class) =
  Exists (x ≠ zeroM group)
    (\ x-nonzero ->
      classOf classes x x-nonzero ≡ class)
SourceClass {c = c} {group = group} classes x top =
  (x ≡ zeroM group) × Top {c}

HasMatchingLeadingClass :
  {a c r : Level}
  {M : Set a}
  {Class : Set c}
  {R : Set r}
  {group : OrderedAbelianGroup M}
  (classes : FiniteArchimedeanClasses group Class)
  (reals : RealLine R) ->
  M ->
  HahnSeries classes reals ->
  Set (a ⊔ c ⊔ r)
HasMatchingLeadingClass {Class = Class} classes reals x series =
  Exists (WithTop Class)
    (\ leading ->
      LeadingIndex classes reals series leading
      ×
      SourceClass classes x leading)

record IsOrderedAdditiveEmbedding
  {a c r : Level}
  {M : Set a}
  {Class : Set c}
  {R : Set r}
  (group : OrderedAbelianGroup M)
  (classes : FiniteArchimedeanClasses group Class)
  (reals : RealLine R)
  (embedding : M -> HahnSeries classes reals) :
  Set (a ⊔ c ⊔ r) where

  field
    map-zero :
      (class : Class) ->
      coefficient (embedding (zeroM group)) class ≡ zeroR reals

    map-add :
      (x y : M) ->
      (class : Class) ->
      coefficient (embedding (addM group x y)) class
      ≡
      addR reals
        (coefficient (embedding x) class)
        (coefficient (embedding y) class)

    order-preserving :
      (x y : M) ->
      lessOrEqualM group x y ->
      LexicographicallyLessOrEqual
        classes reals (embedding x) (embedding y)

    injective :
      (x y : M) ->
      SeriesEqual (embedding x) (embedding y) ->
      x ≡ y

hahnEmbedding-isOrderedAddMonoid :
  {a c r : Level} ->
  Set (lsuc (a ⊔ c ⊔ r))
hahnEmbedding-isOrderedAddMonoid {a} {c} {r} =
  (M : Set a) ->
  (group : OrderedAbelianGroup M) ->
  (Class : Set c) ->
  (classes : FiniteArchimedeanClasses group Class) ->
  (R : Set r) ->
  (reals : RealLine R) ->
  Exists (M -> HahnSeries classes reals)
    (\ embedding ->
      IsOrderedAdditiveEmbedding group classes reals embedding
      ×
      ((x : M) ->
        HasMatchingLeadingClass classes reals x (embedding x)))
