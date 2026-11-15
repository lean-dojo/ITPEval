-- Statement-only formalization of "The Independence of the Parallel Postulate" from Hundred
-- Theorems item 012: the Klein disk over the real field satisfies Tarski's axioms other than
-- the Euclidean parallel axiom, whose negation holds. This file contains no proof.

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : {a : Level} -> Set a -> Set a
Not A = A -> Bottom

NotEqual : {a : Level} {A : Set a} -> A -> A -> Set a
NotEqual x y = Not (x == y)

record _and_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor both
  field
    first  : A
    second : B

data _or_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  left  : A -> A or B
  right : B -> A or B

record Exists {a p : Level} (A : Set a) (P : A -> Set p) :
  Set (a ⊔ p) where
  constructor witness
  field
    value    : A
    property : P value

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zero one : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set

    one-not-zero :
      NotEqual one zero

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zero == x
    add-inverse :
      (x : R) -> add x (negate x) == zero

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x one == x
    multiply-zero :
      (x : R) -> multiply x zero == zero
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    multiply-inverse :
      (x : R) ->
      NotEqual x zero ->
      multiply x (inverse x) == one

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zero x ->
      lessOrEqual zero y ->
      lessOrEqual zero (multiply x y)
    zero-less-than-one :
      lessOrEqual zero one and NotEqual zero one

    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum) and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and NotEqual x y

record Vector2 (R : Set) : Set where
  constructor vector
  field
    x-coordinate : R
    y-coordinate : R

open Vector2

vectorAdd :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector2 R ->
  Vector2 R ->
  Vector2 R
vectorAdd reals u v =
  vector
    (add reals (x-coordinate u) (x-coordinate v))
    (add reals (y-coordinate u) (y-coordinate v))

vectorScale :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Vector2 R ->
  Vector2 R
vectorScale reals scalar v =
  vector
    (multiply reals scalar (x-coordinate v))
    (multiply reals scalar (y-coordinate v))

dot :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector2 R ->
  Vector2 R ->
  R
dot reals u v =
  add reals
    (multiply reals (x-coordinate u) (x-coordinate v))
    (multiply reals (y-coordinate u) (y-coordinate v))

squaredNorm :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector2 R ->
  R
squaredNorm reals v =
  dot reals v v

InsideUnitDisk :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector2 R ->
  Set
InsideUnitDisk reals v =
  StrictLess reals
    (squaredNorm reals v)
    (one reals)

Between :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector2 R ->
  Vector2 R ->
  Vector2 R ->
  Set
Between reals y x z =
  Exists _
    (\ t ->
      lessOrEqual reals (zero reals) t and
      (lessOrEqual reals t (one reals) and
       y ==
       vectorAdd reals
         (vectorScale reals
           (subtract reals (one reals) t)
           x)
         (vectorScale reals t z)))

kleinDistance :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector2 R ->
  Vector2 R ->
  R
kleinDistance reals x y =
  subtract reals
    (divide reals
      (square reals
        (subtract reals
          (one reals)
          (dot reals x y)))
      (multiply reals
        (subtract reals
          (one reals)
          (squaredNorm reals x))
        (subtract reals
          (one reals)
          (squaredNorm reals y))))
    (one reals)

record KleinPlane
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set₁ where

  field
    Point : Set
    dest : Point -> Vector2 R

    dest-inside :
      (p : Point) ->
      InsideUnitDisk reals (dest p)

    dest-injective :
      (p q : Point) ->
      dest p == dest q ->
      p == q

    dest-surjective :
      (v : Vector2 R) ->
      InsideUnitDisk reals v ->
      Exists Point (\ p -> dest p == v)

open KleinPlane

Betweenness :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Point plane ->
  Point plane ->
  Point plane ->
  Set
Betweenness reals plane a b c =
  Between reals
    (dest plane b)
    (dest plane a)
    (dest plane c)

PlaneDistance :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Point plane ->
  Point plane ->
  R
PlaneDistance reals plane a b =
  kleinDistance reals
    (dest plane a)
    (dest plane b)

SegmentCongruent :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Point plane ->
  Point plane ->
  Point plane ->
  Point plane ->
  Set
SegmentCongruent reals plane a b c d =
  PlaneDistance reals plane a b ==
  PlaneDistance reals plane c d

TarskiAxiom1 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Set
TarskiAxiom1 reals plane =
  (a b : Point plane) ->
  SegmentCongruent reals plane a b b a

TarskiAxiom2 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Set
TarskiAxiom2 reals plane =
  (a b p q r s : Point plane) ->
  SegmentCongruent reals plane a b p q ->
  SegmentCongruent reals plane a b r s ->
  SegmentCongruent reals plane p q r s

TarskiAxiom3 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Set
TarskiAxiom3 reals plane =
  (a b c : Point plane) ->
  SegmentCongruent reals plane a b c c ->
  a == b

TarskiAxiom4 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Set
TarskiAxiom4 reals plane =
  (a q b c : Point plane) ->
  Exists (Point plane)
    (\ x ->
      Betweenness reals plane q a x and
      SegmentCongruent reals plane a x b c)

TarskiAxiom5 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Set
TarskiAxiom5 reals plane =
  (a b c x a' b' c' x' : Point plane) ->
  NotEqual a b ->
  SegmentCongruent reals plane a b a' b' ->
  SegmentCongruent reals plane a c a' c' ->
  SegmentCongruent reals plane b c b' c' ->
  Betweenness reals plane a b x ->
  Betweenness reals plane a' b' x' ->
  SegmentCongruent reals plane b x b' x' ->
  SegmentCongruent reals plane c x c' x'

TarskiAxiom6 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Set
TarskiAxiom6 reals plane =
  (a b : Point plane) ->
  Betweenness reals plane a b a ->
  a == b

TarskiAxiom7 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Set
TarskiAxiom7 reals plane =
  (a b c p q : Point plane) ->
  Betweenness reals plane a p c ->
  Betweenness reals plane b q c ->
  Exists (Point plane)
    (\ x ->
      Betweenness reals plane p x b and
      Betweenness reals plane q x a)

TarskiAxiom8 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Set
TarskiAxiom8 reals plane =
  Exists (Point plane)
    (\ a ->
      Exists (Point plane)
        (\ b ->
          Exists (Point plane)
            (\ c ->
              Not (Betweenness reals plane a b c) and
              (Not (Betweenness reals plane b c a) and
               Not (Betweenness reals plane c a b)))))

TarskiAxiom9 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Set
TarskiAxiom9 reals plane =
  (p q a b c : Point plane) ->
  NotEqual p q ->
  SegmentCongruent reals plane a p a q ->
  SegmentCongruent reals plane b p b q ->
  SegmentCongruent reals plane c p c q ->
  Betweenness reals plane a b c or
  (Betweenness reals plane b c a or
   Betweenness reals plane c a b)

TarskiAxiom10 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Set
TarskiAxiom10 reals plane =
  (a b c d t : Point plane) ->
  Betweenness reals plane a d t ->
  Betweenness reals plane b d c ->
  NotEqual a d ->
  Exists (Point plane)
    (\ x ->
      Exists (Point plane)
        (\ y ->
          Betweenness reals plane a b x and
          (Betweenness reals plane a c y and
           Betweenness reals plane x t y)))

TarskiAxiom11 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (plane : KleinPlane reals) ->
  Set₁
TarskiAxiom11 reals plane =
  (X Y : Point plane -> Set) ->
  Exists (Point plane)
    (\ a ->
      (x y : Point plane) ->
      X x and Y y ->
      Betweenness reals plane a x y) ->
  Exists (Point plane)
    (\ b ->
      (x y : Point plane) ->
      X x and Y y ->
      Betweenness reals plane x b y)

record TarskiAxiomsExceptEuclid
  {R : Set}
  (reals : CompleteOrderedField R)
  (plane : KleinPlane reals) :
  Set₁ where

  field
    axiom1  : TarskiAxiom1 reals plane
    axiom2  : TarskiAxiom2 reals plane
    axiom3  : TarskiAxiom3 reals plane
    axiom4  : TarskiAxiom4 reals plane
    axiom5  : TarskiAxiom5 reals plane
    axiom6  : TarskiAxiom6 reals plane
    axiom7  : TarskiAxiom7 reals plane
    axiom8  : TarskiAxiom8 reals plane
    axiom9  : TarskiAxiom9 reals plane
    axiom11 : TarskiAxiom11 reals plane

record KleinRealCountermodel : Set₂ where
  field
    Real : Set
    real-field : CompleteOrderedField Real
    klein-plane : KleinPlane real-field
    absolute-geometry :
      TarskiAxiomsExceptEuclid real-field klein-plane
    parallel-postulate-fails :
      Not (TarskiAxiom10 real-field klein-plane)

the-independence-of-the-parallel-postulate : Set₂
the-independence-of-the-parallel-postulate =
  KleinRealCountermodel
