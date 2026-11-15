-- Statement-only formalization of PutnamBench corpus artifact putnam_2016_b3:
-- every finite set of real-plane points whose point-triples have triangle area at
-- most one is contained in a triangle of area exactly four. This file contains no proof.

module Putnam2016B3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
import Agda.Builtin.Nat as NatB

infix 4 _!=_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

Nat : Set
Nat = NatB.Nat

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (NatB.suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (NatB.suc n)

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zero one : R
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      one != zero

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
      x != zero ->
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
      lessOrEqual zero one and zero != one

    fromNat-zero :
      fromNat NatB.zero == zero
    fromNat-successor :
      (n : Nat) -> fromNat (NatB.suc n) == add (fromNat n) one
    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual zero (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual zero x ->
      multiply (squareRoot x) (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual x zero ->
      squareRoot x == zero
    square-root-unique :
      (x y : R) ->
      lessOrEqual zero y ->
      multiply y y == x ->
      y == squareRoot x

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

two :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
two reals =
  add reals (one reals) (one reals)

four :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
four reals =
  add reals (two reals) (two reals)

half :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
half reals =
  inverse reals (two reals)

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

addPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R
addPoint reals p q =
  point
    (add reals (x-coordinate p) (x-coordinate q))
    (add reals (y-coordinate p) (y-coordinate q))

scalePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Point R ->
  Point R
scalePoint reals scalar p =
  point
    (multiply reals scalar (x-coordinate p))
    (multiply reals scalar (y-coordinate p))

weightedPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Point R ->
  Point R ->
  Point R ->
  Point R
weightedPoint reals alpha beta gamma a b c =
  addPoint reals
    (addPoint reals
      (scalePoint reals alpha a)
      (scalePoint reals beta b))
    (scalePoint reals gamma c)

doubleSignedArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
doubleSignedArea reals a b c =
  subtract reals
    (multiply reals
      (subtract reals (x-coordinate b) (x-coordinate a))
      (subtract reals (y-coordinate c) (y-coordinate a)))
    (multiply reals
      (subtract reals (y-coordinate b) (y-coordinate a))
      (subtract reals (x-coordinate c) (x-coordinate a)))

triangleArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
triangleArea reals a b c =
  multiply reals
    (half reals)
    (squareRoot reals
      (square reals (doubleSignedArea reals a b c)))

Nonnegative :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Nonnegative reals x =
  lessOrEqual reals (zero reals) x

InTriangle :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Set
InTriangle {R} reals a b c p =
  Exists R
    (\ alpha ->
      Exists R
        (\ beta ->
          Exists R
            (\ gamma ->
              Nonnegative reals alpha
              and
              (Nonnegative reals beta
              and
              (Nonnegative reals gamma
              and
              (add reals (add reals alpha beta) gamma == one reals
              and
              p == weightedPoint reals alpha beta gamma a b c))))))

module Putnam2016B3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (n : Nat)
  (S : Fin n -> Point R) where

  proposition : Set
  proposition =
    ((i j k : Fin n) ->
      lessOrEqual reals
        (triangleArea reals (S i) (S j) (S k))
        (one reals)) ->
    Exists (Point R)
      (\ a ->
        Exists (Point R)
          (\ b ->
            Exists (Point R)
              (\ c ->
                triangleArea reals a b c == four reals
                and
                ((i : Fin n) ->
                  InTriangle reals a b c (S i)))))

putnam-2016-b3 : Set1
putnam-2016-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  (S : Fin n -> Point R) ->
  Putnam2016B3Statement.proposition reals n S
