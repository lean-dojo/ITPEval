-- Statement-only formalization of thousand-theorems corpus artifact Q1194053,
-- "Metrization theorems": every T3 topological space with a second-countable
-- topology admits a real-valued metric inducing exactly that topology. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module Q1194053_metrization_theorems where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _!=_ _<=N_ _<=Z_ _<=Q_ _<Q_ _≈E_ _<=E_ _<E_
infixl 6 _+N_ _+Z_ _+Q_ _+E_
infixl 7 _*N_ _*Z_

data Bottom {a : Level} : Set a where

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

_+N_ :
  Nat ->
  Nat ->
  Nat
zero +N n =
  n
suc m +N n =
  suc (m +N n)

_*N_ :
  Nat ->
  Nat ->
  Nat
zero *N n =
  zero
suc m *N n =
  n +N (m *N n)

data _<=N_ :
  Nat ->
  Nat ->
  Set where

  zero<= :
    {n : Nat} ->
    zero <=N n

  suc<= :
    {m n : Nat} ->
    m <=N n ->
    suc m <=N suc n

-- Integers are exact differences of natural numbers.
record Integer : Set where
  constructor integer
  field
    positivePart :
      Nat

    negativePart :
      Nat

naturalInteger :
  Nat ->
  Integer
naturalInteger n =
  integer n zero

_+Z_ :
  Integer ->
  Integer ->
  Integer
integer p n +Z integer q m =
  integer
    (p +N q)
    (n +N m)

negateZ :
  Integer ->
  Integer
negateZ (integer p n) =
  integer n p

_*Z_ :
  Integer ->
  Integer ->
  Integer
integer p n *Z integer q m =
  integer
    ((p *N q) +N (n *N m))
    ((p *N m) +N (n *N q))

_<=Z_ :
  Integer ->
  Integer ->
  Set
integer p n <=Z integer q m =
  (p +N m) <=N (q +N n)

-- A positive denominator is stored as one plus a natural number.
data Positive : Set where
  onePlus :
    Nat ->
    Positive

positiveValue :
  Positive ->
  Nat
positiveValue (onePlus n) =
  suc n

_*P_ :
  Positive ->
  Positive ->
  Positive
onePlus m *P onePlus n =
  onePlus ((m +N n) +N (m *N n))

record Rational : Set where
  constructor fraction
  field
    numerator :
      Integer

    denominator :
      Positive

scaleInteger :
  Integer ->
  Positive ->
  Integer
scaleInteger z d =
  z *Z naturalInteger (positiveValue d)

_+Q_ :
  Rational ->
  Rational ->
  Rational
fraction x xd +Q fraction y yd =
  fraction
    ((scaleInteger x yd) +Z (scaleInteger y xd))
    (xd *P yd)

negateQ :
  Rational ->
  Rational
negateQ (fraction x xd) =
  fraction (negateZ x) xd

_<=Q_ :
  Rational ->
  Rational ->
  Set
fraction x xd <=Q fraction y yd =
  scaleInteger x yd <=Z scaleInteger y xd

_<Q_ :
  Rational ->
  Rational ->
  Set
x <Q y =
  Both
    (x <=Q y)
    (Not (y <=Q x))

naturalRational :
  Nat ->
  Rational
naturalRational n =
  fraction
    (naturalInteger n)
    (onePlus zero)

rationalZero :
  Rational
rationalZero =
  naturalRational zero

unitFraction :
  Nat ->
  Rational
unitFraction n =
  fraction
    (naturalInteger (suc zero))
    (onePlus n)

RealExpression :
  Set
RealExpression =
  Nat -> Rational

constant :
  Rational ->
  RealExpression
constant q n =
  q

naturalExpression :
  Nat ->
  RealExpression
naturalExpression n =
  constant (naturalRational n)

_+E_ :
  RealExpression ->
  RealExpression ->
  RealExpression
(x +E y) n =
  x n +Q y n

Close :
  Rational ->
  Rational ->
  Rational ->
  Set
Close x y tolerance =
  Both
    (x <=Q (y +Q tolerance))
    (y <=Q (x +Q tolerance))

-- Every classical real admits a rational approximation with this regular
-- Cauchy modulus.
Regular :
  RealExpression ->
  Set
Regular x =
  (m n : Nat) ->
  Close
    (x m)
    (x n)
    (unitFraction m +Q unitFraction n)

-- Real numbers are fixed regular Cauchy presentations. The relations below
-- are equality and order on their Cauchy completion.
record Real : Set where
  constructor real
  field
    approximation :
      RealExpression

    regular :
      Regular approximation

realExpression :
  Real ->
  RealExpression
realExpression =
  Real.approximation

_≈E_ :
  RealExpression ->
  RealExpression ->
  Set
x ≈E y =
  (precision : Nat) ->
  Σ Nat
    (λ threshold ->
      (index : Nat) ->
      threshold <=N index ->
      Close
        (x index)
        (y index)
        (unitFraction precision))

_<=E_ :
  RealExpression ->
  RealExpression ->
  Set
x <=E y =
  (precision : Nat) ->
  Σ Nat
    (λ threshold ->
      (index : Nat) ->
      threshold <=N index ->
      x index <=Q
      (y index +Q unitFraction precision))

_<E_ :
  RealExpression ->
  RealExpression ->
  Set
x <E y =
  Σ Rational
    (λ gap ->
      Both
        (rationalZero <Q gap)
        (Σ Nat
          (λ threshold ->
            (index : Nat) ->
            threshold <=N index ->
            (x index +Q gap) <=Q y index)))

RealEqual :
  Real ->
  Real ->
  Set
RealEqual x y =
  realExpression x ≈E realExpression y

RealNonnegative :
  Real ->
  Set
RealNonnegative x =
  naturalExpression zero <=E realExpression x

RealPositive :
  Real ->
  Set
RealPositive x =
  naturalExpression zero <E realExpression x

RealStrictLess :
  Real ->
  Real ->
  Set
RealStrictLess x y =
  realExpression x <E realExpression y

RealZero :
  Real ->
  Set
RealZero x =
  realExpression x ≈E naturalExpression zero

RealLessOrEqualSum :
  Real ->
  Real ->
  Real ->
  Set
RealLessOrEqualSum x y z =
  realExpression x <=E
  (realExpression y +E realExpression z)

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
Empty {a} _ =
  Bottom {a}

Union :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Subset X ->
  Subset X
Union U V x =
  Either (U x) (V x)

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
  Iff (U x) (V x)

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
      SubsetOf (close Empty) Empty

    subset-close :
      (U : Subset X) ->
      SubsetOf U (close U)

    close-union-forward :
      (U V : Subset X) ->
      SubsetOf
        (close (Union U V))
        (Union (close U) (close V))

    close-union-backward :
      (U V : Subset X) ->
      SubsetOf
        (Union (close U) (close V))
        (close (Union U V))

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

T0Space :
  {a : Level} ->
  {X : Set a} ->
  TopologicalSpace X ->
  Set (lsuc a)
T0Space {X = X} topology =
  (x y : X) ->
  x != y ->
  Either
    (Σ (Subset X)
      (λ U ->
        Both
          (IsOpen topology U)
          (Both
            (U x)
            (Not (U y)))))
    (Σ (Subset X)
      (λ U ->
        Both
          (IsOpen topology U)
          (Both
            (U y)
            (Not (U x)))))

RegularSpace :
  {a : Level} ->
  {X : Set a} ->
  TopologicalSpace X ->
  Set (lsuc a)
RegularSpace {X = X} topology =
  (U : Subset X) ->
  IsOpen topology U ->
  (x : X) ->
  U x ->
  Σ (Subset X)
    (λ V ->
      Both
        (IsOpen topology V)
        (Both
          (V x)
          (SubsetOf (close topology V) U)))

T3Space :
  {a : Level} ->
  {X : Set a} ->
  TopologicalSpace X ->
  Set (lsuc a)
T3Space topology =
  Both
    (T0Space topology)
    (RegularSpace topology)

SecondCountableTopology :
  {a : Level} ->
  {X : Set a} ->
  TopologicalSpace X ->
  Set (lsuc a)
SecondCountableTopology {X = X} topology =
  Σ (Nat -> Subset X)
    (λ basis ->
      Both
        ((n : Nat) ->
          IsOpen topology (basis n))
        ((U : Subset X) ->
          IsOpen topology U ->
          (x : X) ->
          U x ->
          Σ Nat
            (λ n ->
              Both
                (basis n x)
                (SubsetOf (basis n) U))))

record MetricSpace
  {a : Level}
  (X : Set a) :
  Set a where

  field
    distance :
      X ->
      X ->
      Real

    distance-nonnegative :
      (x y : X) ->
      RealNonnegative (distance x y)

    distance-self :
      (x : X) ->
      RealZero (distance x x)

    distance-zero-only :
      (x y : X) ->
      RealZero (distance x y) ->
      x == y

    distance-symmetric :
      (x y : X) ->
      RealEqual (distance x y) (distance y x)

    distance-triangle :
      (x y z : X) ->
      RealLessOrEqualSum
        (distance x z)
        (distance x y)
        (distance y z)

open MetricSpace

MetricClosure :
  {a : Level} ->
  {X : Set a} ->
  MetricSpace X ->
  Subset X ->
  X ->
  Set a
MetricClosure {X = X} metric U x =
  (epsilon : Real) ->
  RealPositive epsilon ->
  Σ X
    (λ y ->
      Both
        (U y)
        (RealStrictLess
          (distance metric x y)
          epsilon))

InducesTopology :
  {a : Level} ->
  {X : Set a} ->
  TopologicalSpace X ->
  MetricSpace X ->
  Set (lsuc a)
InducesTopology {X = X} topology metric =
  (U : Subset X) ->
  (x : X) ->
  Iff
    (close topology U x)
    (MetricClosure metric U x)

MetrizableSpace :
  {a : Level} ->
  {X : Set a} ->
  TopologicalSpace X ->
  Set (lsuc a)
MetrizableSpace {X = X} topology =
  Σ (MetricSpace X)
    (λ metric ->
      InducesTopology topology metric)

metrization-theorems :
  {a : Level} ->
  Set (lsuc a)
metrization-theorems {a} =
  (X : Set a) ->
  (topology : TopologicalSpace X) ->
  T3Space topology ->
  SecondCountableTopology topology ->
  MetrizableSpace topology
