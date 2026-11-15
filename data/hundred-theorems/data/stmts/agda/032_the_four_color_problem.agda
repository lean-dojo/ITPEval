-- Statement-only formalization of "The Four Color Problem" from Hundred Theorems item 032:
-- every simple map of open connected regions over an arbitrary modeled real plane is
-- colorable with at most four colors. This file contains no proof.

module FourColorProblem where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

record Both (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where
  constructor witness
  field
    value : A
    property : P value

data NatLessOrEqual : Nat -> Nat -> Set where
  zero-less-or-equal :
    {n : Nat} ->
    NatLessOrEqual zero n
  successors-less-or-equal :
    {m n : Nat} ->
    NatLessOrEqual m n ->
    NatLessOrEqual (suc m) (suc n)

NatStrictLess : Nat -> Nat -> Set
NatStrictLess m n =
  NatLessOrEqual (suc m) n

record RealStructure : Set1 where
  field
    Val : Set
    lessOrEqual : Val -> Val -> Set
    supremum : (Val -> Set) -> Val
    add : Val -> Val -> Val
    zeroR : Val
    negate : Val -> Val
    multiply : Val -> Val -> Val
    oneR : Val
    inverse : Val -> Val

open RealStructure

RealEqual :
  (R : RealStructure) ->
  Val R ->
  Val R ->
  Set
RealEqual R x y =
  Both
    (lessOrEqual R x y)
    (lessOrEqual R y x)

UpperBounds :
  (R : RealStructure) ->
  (Val R -> Set) ->
  Val R ->
  Set
UpperBounds R body upper =
  (y : Val R) ->
  body y ->
  lessOrEqual R y upper

DownwardClosure :
  (R : RealStructure) ->
  (Val R -> Set) ->
  Val R ->
  Set
DownwardClosure R body x =
  Exists (Val R)
    (\ y ->
      Both
        (body y)
        (lessOrEqual R x y))

NonemptySet :
  {A : Set} ->
  (A -> Set) ->
  Set
NonemptySet {A} body =
  Exists A body

HasUpperBound :
  (R : RealStructure) ->
  (Val R -> Set) ->
  Set
HasUpperBound R body =
  NonemptySet (UpperBounds R body)

HasSupremum :
  (R : RealStructure) ->
  (Val R -> Set) ->
  Set
HasSupremum R body =
  Both
    (NonemptySet body)
    (HasUpperBound R body)

record RealAxioms (R : RealStructure) : Set1 where
  field
    order-reflexive :
      (x : Val R) ->
      lessOrEqual R x x
    order-transitive :
      (x y z : Val R) ->
      lessOrEqual R x y ->
      lessOrEqual R y z ->
      lessOrEqual R x z
    supremum-upper-bound :
      (body : Val R -> Set) ->
      HasSupremum R body ->
      UpperBounds R body (supremum R body)
    supremum-total :
      (body : Val R -> Set) ->
      (x : Val R) ->
      HasSupremum R body ->
      Either
        (DownwardClosure R body x)
        (lessOrEqual R (supremum R body) x)
    add-monotone :
      (x y z : Val R) ->
      lessOrEqual R y z ->
      lessOrEqual R (add R x y) (add R x z)
    add-commutative :
      (x y : Val R) ->
      RealEqual R (add R x y) (add R y x)
    add-associative :
      (x y z : Val R) ->
      RealEqual R
        (add R x (add R y z))
        (add R (add R x y) z)
    zero-add :
      (x : Val R) ->
      RealEqual R (add R (zeroR R) x) x
    add-negate :
      (x : Val R) ->
      RealEqual R (add R x (negate R x)) (zeroR R)
    multiply-monotone :
      (x y z : Val R) ->
      lessOrEqual R (zeroR R) x ->
      lessOrEqual R y z ->
      lessOrEqual R
        (multiply R x y)
        (multiply R x z)
    multiply-commutative :
      (x y : Val R) ->
      RealEqual R
        (multiply R x y)
        (multiply R y x)
    multiply-associative :
      (x y z : Val R) ->
      RealEqual R
        (multiply R x (multiply R y z))
        (multiply R (multiply R x y) z)
    multiply-add :
      (x y z : Val R) ->
      RealEqual R
        (multiply R x (add R y z))
        (add R
          (multiply R x y)
          (multiply R x z))
    one-multiply :
      (x : Val R) ->
      RealEqual R (multiply R (oneR R) x) x
    multiply-inverse :
      (x : Val R) ->
      Not (RealEqual R x (zeroR R)) ->
      RealEqual R
        (multiply R x (inverse R x))
        (oneR R)
    one-not-zero :
      Not (RealEqual R (oneR R) (zeroR R))

record RealModel : Set1 where
  field
    structure : RealStructure
    axioms : RealAxioms structure

open RealModel

record Point (R : RealStructure) : Set where
  constructor point
  field
    x-coordinate : Val R
    y-coordinate : Val R

open Point

Region : RealStructure -> Set1
Region R =
  Point R -> Set

PlaneMap : RealStructure -> Set1
PlaneMap R =
  Point R -> Point R -> Set

record Interval (R : RealStructure) : Set where
  constructor interval
  field
    left-endpoint : Val R
    right-endpoint : Val R

open Interval

record Rectangle (R : RealStructure) : Set where
  constructor rectangle
  field
    horizontal : Interval R
    vertical : Interval R

open Rectangle

InInterval :
  {R : RealStructure} ->
  Interval R ->
  Val R ->
  Set
InInterval {R} bounds t =
  Both
    (Not (lessOrEqual R t (left-endpoint bounds)))
    (Not (lessOrEqual R (right-endpoint bounds) t))

InRectangle :
  {R : RealStructure} ->
  Rectangle R ->
  Region R
InRectangle bounds p =
  Both
    (InInterval (horizontal bounds) (x-coordinate p))
    (InInterval (vertical bounds) (y-coordinate p))

RegionUnion :
  {R : RealStructure} ->
  Region R ->
  Region R ->
  Region R
RegionUnion leftRegion rightRegion p =
  Either
    (leftRegion p)
    (rightRegion p)

RegionIntersection :
  {R : RealStructure} ->
  Region R ->
  Region R ->
  Region R
RegionIntersection leftRegion rightRegion p =
  Both
    (leftRegion p)
    (rightRegion p)

RegionNonempty :
  {R : RealStructure} ->
  Region R ->
  Set
RegionNonempty {R} body =
  Exists (Point R) body

Subregion :
  {R : RealStructure} ->
  Region R ->
  Region R ->
  Set
Subregion {R} leftRegion rightRegion =
  (p : Point R) ->
  leftRegion p ->
  rightRegion p

Meet :
  {R : RealStructure} ->
  Region R ->
  Region R ->
  Set
Meet leftRegion rightRegion =
  RegionNonempty
    (RegionIntersection leftRegion rightRegion)

record PlainMap
  {R : RealStructure}
  (m : PlaneMap R) :
  Set where

  field
    symmetric :
      (p q : Point R) ->
      m p q ->
      m q p
    transitive :
      (p q : Point R) ->
      m p q ->
      Subregion (m q) (m p)

Cover :
  {R : RealStructure} ->
  PlaneMap R ->
  Region R
Cover m p =
  m p p

Submap :
  {R : RealStructure} ->
  PlaneMap R ->
  PlaneMap R ->
  Set
Submap {R} smaller larger =
  (p : Point R) ->
  Subregion (smaller p) (larger p)

AtMostRegions :
  {R : RealStructure} ->
  Nat ->
  PlaneMap R ->
  Set
AtMostRegions {R} n m =
  Exists (Nat -> Point R)
    (\ representatives ->
      (p : Point R) ->
      Cover m p ->
      Exists Nat
        (\ i ->
          Both
            (NatStrictLess i n)
            (m (representatives i) p)))

OpenRegion :
  {R : RealStructure} ->
  Region R ->
  Set
OpenRegion {R} body =
  (p : Point R) ->
  body p ->
  Exists (Rectangle R)
    (\ bounds ->
      Both
        (InRectangle bounds p)
        (Subregion (InRectangle bounds) body))

Closure :
  {R : RealStructure} ->
  Region R ->
  Region R
Closure {R} body p =
  (bounds : Rectangle R) ->
  InRectangle bounds p ->
  Meet body (InRectangle bounds)

Connected :
  {R : RealStructure} ->
  Region R ->
  Set1
Connected body =
  (leftOpen rightOpen : Region _) ->
  OpenRegion leftOpen ->
  OpenRegion rightOpen ->
  Subregion body (RegionUnion leftOpen rightOpen) ->
  Meet leftOpen body ->
  Meet rightOpen body ->
  Meet leftOpen rightOpen

record SimpleMap
  {R : RealStructure}
  (m : PlaneMap R) :
  Set1 where

  field
    plain :
      PlainMap m
    open-region :
      (p : Point R) ->
      OpenRegion (m p)
    connected-region :
      (p : Point R) ->
      Connected (m p)

record FiniteSimpleMap
  {R : RealStructure}
  (m : PlaneMap R) :
  Set1 where

  field
    simple :
      SimpleMap m
    finite :
      Exists Nat
        (\ n ->
          AtMostRegions n m)

Border :
  {R : RealStructure} ->
  PlaneMap R ->
  Point R ->
  Point R ->
  Region R
Border m p q =
  RegionIntersection
    (Closure (m p))
    (Closure (m q))

CornerMap :
  {R : RealStructure} ->
  PlaneMap R ->
  Point R ->
  PlaneMap R
CornerMap m p q r =
  Both
    (m q r)
    (Closure (m q) p)

NotCorner :
  {R : RealStructure} ->
  PlaneMap R ->
  Region R
NotCorner m p =
  AtMostRegions 2 (CornerMap m p)

Adjacent :
  {R : RealStructure} ->
  PlaneMap R ->
  Point R ->
  Point R ->
  Set
Adjacent m p q =
  Both
    (Not (m p q))
    (Meet
      (NotCorner m)
      (Border m p q))

record Coloring
  {R : RealStructure}
  (m k : PlaneMap R) :
  Set where

  field
    plain :
      PlainMap k
    cover :
      Subregion (Cover k) (Cover m)
    consistent :
      Submap m k
    separates-adjacent :
      (p q : Point R) ->
      Adjacent m p q ->
      Not (k p q)

ColorableWith :
  {R : RealStructure} ->
  Nat ->
  PlaneMap R ->
  Set1
ColorableWith {R} n m =
  Exists (PlaneMap R)
    (\ coloring ->
      Both
        (Coloring m coloring)
        (AtMostRegions n coloring))

four-color-finite : Set1
four-color-finite =
  (Rmodel : RealModel) ->
  (m : PlaneMap (structure Rmodel)) ->
  FiniteSimpleMap m ->
  ColorableWith 4 m

four-color : Set1
four-color =
  (Rmodel : RealModel) ->
  (m : PlaneMap (structure Rmodel)) ->
  SimpleMap m ->
  ColorableWith 4 m

record BothFourColorClaims : Set1 where
  field
    finite-case : four-color-finite
    general-case : four-color

the-four-color-problem : Set1
the-four-color-problem =
  BothFourColorClaims
