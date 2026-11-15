-- Statement-only formalization of thousand-theorems corpus artifact Q245098,
-- "Intermediate value theorem": a function continuous on a closed interval
-- in a dense conditionally complete linear order takes every target value
-- between its endpoint values. This file contains no proof.

{-# OPTIONS --safe #-}

module Q245098_intermediate_value_theorem where

open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} proposition =
  proposition -> Bottom {a}

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

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Pair
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor pair
  field
    first  : A
    second : B

record LinearOrder
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    lessOrEqual :
      A ->
      A ->
      Set a

    order-reflexive :
      (x : A) ->
      lessOrEqual x x

    order-transitive :
      (x y z : A) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z

    order-antisymmetric :
      (x y : A) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y

    order-total :
      (x y : A) ->
      Either
        (lessOrEqual x y)
        (lessOrEqual y x)

    order-decidable :
      (x y : A) ->
      Either
        (lessOrEqual x y)
        (Not (lessOrEqual x y))

open LinearOrder

StrictLess :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  A ->
  A ->
  Set a
StrictLess order x y =
  Both
    (lessOrEqual order x y)
    (Not (x == y))

UpperBound :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  (A -> Set a) ->
  A ->
  Set a
UpperBound {A = A} order P upper =
  (x : A) ->
  P x ->
  lessOrEqual order x upper

LowerBound :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  (A -> Set a) ->
  A ->
  Set a
LowerBound {A = A} order P lower =
  (x : A) ->
  P x ->
  lessOrEqual order lower x

BoundedAbove :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  (A -> Set a) ->
  Set a
BoundedAbove {A = A} order P =
  Exists A (UpperBound order P)

BoundedBelow :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  (A -> Set a) ->
  Set a
BoundedBelow {A = A} order P =
  Exists A (LowerBound order P)

Nonempty :
  {a : Level} ->
  {A : Set a} ->
  (A -> Set a) ->
  Set a
Nonempty {A = A} P =
  Exists A P

IsLeastUpperBound :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  (A -> Set a) ->
  A ->
  Set a
IsLeastUpperBound {A = A} order P supremum =
  Both
    (UpperBound order P supremum)
    ((upper : A) ->
      UpperBound order P upper ->
      lessOrEqual order supremum upper)

IsGreatestLowerBound :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  (A -> Set a) ->
  A ->
  Set a
IsGreatestLowerBound {A = A} order P infimum =
  Both
    (LowerBound order P infimum)
    ((lower : A) ->
      LowerBound order P lower ->
      lessOrEqual order lower infimum)

record ConditionallyCompleteLinearOrder
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    linearOrder :
      LinearOrder A

    supremum infimum :
      (A -> Set a) ->
      A

    supremum-property :
      (P : A -> Set a) ->
      Nonempty P ->
      BoundedAbove linearOrder P ->
      IsLeastUpperBound linearOrder P (supremum P)

    infimum-property :
      (P : A -> Set a) ->
      Nonempty P ->
      BoundedBelow linearOrder P ->
      IsGreatestLowerBound linearOrder P (infimum P)

open ConditionallyCompleteLinearOrder

record DenselyOrdered
  {a : Level}
  {A : Set a}
  (order : LinearOrder A) :
  Set a where

  field
    dense :
      (x y : A) ->
      StrictLess order x y ->
      Exists A
        (\ z ->
          Both
            (StrictLess order x z)
            (StrictLess order z y))

record TopologicalSpace
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    close :
      (A -> Set a) ->
      A ->
      Set a

    close-congruent :
      (U V : A -> Set a) ->
      ((x : A) -> Iff (U x) (V x)) ->
      (x : A) ->
      Iff (close U x) (close V x)

    close-empty :
      (x : A) ->
      close (\ _ -> Bottom {a}) x ->
      Bottom {a}

    subset-close :
      (U : A -> Set a) ->
      (x : A) ->
      U x ->
      close U x

    close-monotone :
      (U V : A -> Set a) ->
      ((x : A) -> U x -> V x) ->
      (x : A) ->
      close U x ->
      close V x

    close-union-forward :
      (U V : A -> Set a) ->
      (x : A) ->
      close (\ y -> Either (U y) (V y)) x ->
      Either (close U x) (close V x)

    close-union-backward :
      (U V : A -> Set a) ->
      (x : A) ->
      Either (close U x) (close V x) ->
      close (\ y -> Either (U y) (V y)) x

    close-idempotent :
      (U : A -> Set a) ->
      (x : A) ->
      close (close U) x ->
      close U x

open TopologicalSpace

Open :
  {a : Level} ->
  {A : Set a} ->
  TopologicalSpace A ->
  (A -> Set a) ->
  Set a
Open {A = A} topology U =
  (x : A) ->
  close topology (\ y -> Not (U y)) x ->
  Not (U x)

WholeNeighborhood :
  {a : Level} ->
  {A : Set a} ->
  (A -> Set a) ->
  Set a
WholeNeighborhood {A = A} U =
  (y : A) ->
  U y

LeftRayNeighborhood :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  (A -> Set a) ->
  A ->
  Set a
LeftRayNeighborhood {A = A} order U x =
  Exists A
    (\ upper ->
      Both
        (StrictLess order x upper)
        ((y : A) ->
          StrictLess order y upper ->
          U y))

RightRayNeighborhood :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  (A -> Set a) ->
  A ->
  Set a
RightRayNeighborhood {A = A} order U x =
  Exists A
    (\ lower ->
      Both
        (StrictLess order lower x)
        ((y : A) ->
          StrictLess order lower y ->
          U y))

OpenIntervalNeighborhood :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  (A -> Set a) ->
  A ->
  Set a
OpenIntervalNeighborhood {A = A} order U x =
  Exists A
    (\ lower ->
      Exists A
        (\ upper ->
          Both
            (StrictLess order lower x)
            (Both
              (StrictLess order x upper)
              ((y : A) ->
                StrictLess order lower y ->
                StrictLess order y upper ->
                U y))))

OrderOpen :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  (A -> Set a) ->
  Set a
OrderOpen {A = A} order U =
  (x : A) ->
  U x ->
  Either
    (WholeNeighborhood U)
    (Either
      (LeftRayNeighborhood order U x)
      (Either
        (RightRayNeighborhood order U x)
        (OpenIntervalNeighborhood order U x)))

record OrderTopology
  {a : Level}
  {A : Set a}
  (order : LinearOrder A)
  (topology : TopologicalSpace A) :
  Set (lsuc a) where

  field
    open-iff-order-open :
      (U : A -> Set a) ->
      Iff
        (Open topology U)
        (OrderOpen order U)

ProductOpen :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  TopologicalSpace A ->
  TopologicalSpace B ->
  (Pair A B -> Set (a ⊔ b)) ->
  Set (lsuc (a ⊔ b))
ProductOpen {a = a} {b = b} {A = A} {B = B}
  topologyA topologyB W =
  (point : Pair A B) ->
  W point ->
  Exists (A -> Set a)
    (\ U ->
      Exists (B -> Set b)
        (\ V ->
          Both
            (Open topologyA U)
            (Both
              (Open topologyB V)
              (Both
                (U (Pair.first point))
                (Both
                  (V (Pair.second point))
                  ((x : A) ->
                    (y : B) ->
                    U x ->
                    V y ->
                    W (pair x y)))))))

record OrderClosedTopology
  {a : Level}
  {A : Set a}
  (order : LinearOrder A)
  (topology : TopologicalSpace A) :
  Set (lsuc a) where

  field
    order-relation-closed :
      ProductOpen topology topology
        (\ point ->
          Not
            (lessOrEqual order
              (Pair.first point)
              (Pair.second point)))

InClosedInterval :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  A ->
  A ->
  A ->
  Set a
InClosedInterval order lower upper x =
  Both
    (lessOrEqual order lower x)
    (lessOrEqual order x upper)

ContinuousOn :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  TopologicalSpace A ->
  TopologicalSpace B ->
  (A -> B) ->
  (A -> Set a) ->
  Set (lsuc (a ⊔ b))
ContinuousOn {a = a} {b = b} {A = A} {B = B}
  topologyA topologyB function domain =
  (x : A) ->
  domain x ->
  (V : B -> Set b) ->
  Open topologyB V ->
  V (function x) ->
  Exists (A -> Set a)
    (\ U ->
      Both
        (Open topologyA U)
        (Both
          (U x)
          ((y : A) ->
            domain y ->
            U y ->
            V (function y))))

intermediate-value-Icc : Setω
intermediate-value-Icc =
  (a d : Level) ->
  (A : Set a) ->
  (D : Set d) ->
  (completeOrderA : ConditionallyCompleteLinearOrder A) ->
  DenselyOrdered (linearOrder completeOrderA) ->
  (topologyA : TopologicalSpace A) ->
  OrderTopology (linearOrder completeOrderA) topologyA ->
  (orderD : LinearOrder D) ->
  (topologyD : TopologicalSpace D) ->
  OrderClosedTopology orderD topologyD ->
  (lower upper : A) ->
  lessOrEqual (linearOrder completeOrderA) lower upper ->
  (function : A -> D) ->
  ContinuousOn topologyA topologyD function
    (InClosedInterval
      (linearOrder completeOrderA)
      lower
      upper) ->
  (value : D) ->
  lessOrEqual orderD (function lower) value ->
  lessOrEqual orderD value (function upper) ->
  Exists A
    (\ x ->
      Both
        (InClosedInterval
          (linearOrder completeOrderA)
          lower
          upper
          x)
        (function x == value))
