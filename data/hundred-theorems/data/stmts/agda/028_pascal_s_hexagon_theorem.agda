-- Statement-only formalization of "Pascal's Hexagon Theorem" from Hundred Theorems item 028.
-- It states the real affine conic theorem and the projective implication from
-- Pappus's property to the hexamy property.
-- This file contains no proof.

module HundredTheorems028 where

open import Agda.Primitive using (lzero; lsuc)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not proposition = proposition -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
left != right = Not (left == right)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record CompleteArchimedeanOrderedField (R : Set) : Set (lsuc lzero) where
  field
    zero one : R
    add multiply : R -> R -> R
    negate inverse : R -> R
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
      fromNat Agda.Builtin.Nat.zero == zero
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) one
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

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
          ((x : R) -> P x -> lessOrEqual x supremum) and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteArchimedeanOrderedField

subtract :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

square :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

Collinear :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
Collinear reals a b c =
  multiply reals
    (subtract reals (x-coordinate b) (x-coordinate a))
    (subtract reals (y-coordinate c) (y-coordinate a))
  ==
  multiply reals
    (subtract reals (y-coordinate b) (y-coordinate a))
    (subtract reals (x-coordinate c) (x-coordinate a))

record AffineConic
  {R : Set}
  (reals : CompleteArchimedeanOrderedField R) :
  Set where

  field
    x2-coefficient : R
    y2-coefficient : R
    xy-coefficient : R
    x-coefficient  : R
    y-coefficient  : R
    constant       : R

    nonzero-quadratic :
      Not
        (x2-coefficient == zero reals and
         y2-coefficient == zero reals and
         xy-coefficient == zero reals and
         x-coefficient == zero reals and
         y-coefficient == zero reals and
         constant == zero reals)

open AffineConic

OnConic :
  {R : Set} ->
  (reals : CompleteArchimedeanOrderedField R) ->
  AffineConic reals ->
  Point R ->
  Set
OnConic reals conic p =
  add reals
    (multiply reals
      (x2-coefficient conic)
      (square reals (x-coordinate p)))
    (add reals
      (multiply reals
        (y2-coefficient conic)
        (square reals (y-coordinate p)))
      (add reals
        (multiply reals
          (xy-coefficient conic)
          (multiply reals (x-coordinate p) (y-coordinate p)))
        (add reals
          (multiply reals
            (x-coefficient conic)
            (x-coordinate p))
          (add reals
            (multiply reals
              (y-coefficient conic)
              (y-coordinate p))
            (constant conic)))))
  == zero reals

PascalNondegenerate :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Set
PascalNondegenerate reals a b c d e f =
  Not (Collinear reals a c b) and
  Not (Collinear reals a c d) and
  Not (Collinear reals a c f) and
  Not (Collinear reals a e b) and
  Not (Collinear reals a e d) and
  Not (Collinear reals a e f) and
  Not (Collinear reals c e b) and
  Not (Collinear reals c e d) and
  Not (Collinear reals c e f) and
  Not (Collinear reals b d a) and
  Not (Collinear reals b d c) and
  Not (Collinear reals b d e) and
  Not (Collinear reals b f a) and
  Not (Collinear reals b f c) and
  Not (Collinear reals b f e) and
  Not (Collinear reals d f a) and
  Not (Collinear reals d f c) and
  Not (Collinear reals d f e)

PascalIntersections :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Set
PascalIntersections reals a b c d e f p q r =
  Collinear reals p a b and
  Collinear reals p d e and
  Collinear reals q b c and
  Collinear reals q e f and
  Collinear reals r c d and
  Collinear reals r f a

module AffinePascalStatement
  {R : Set}
  (reals : CompleteArchimedeanOrderedField R) where

  proposition : Set
  proposition =
    (conic : AffineConic reals) ->
    (a b c d e f p q r : Point R) ->
    PascalNondegenerate reals a b c d e f ->
    OnConic reals conic a ->
    OnConic reals conic b ->
    OnConic reals conic c ->
    OnConic reals conic d ->
    OnConic reals conic e ->
    OnConic reals conic f ->
    PascalIntersections reals a b c d e f p q r ->
    Collinear reals p q r

pascals-hexagon-theorem : Set (lsuc lzero)
pascals-hexagon-theorem =
  (R : Set) ->
  (reals : CompleteArchimedeanOrderedField R) ->
  AffinePascalStatement.proposition reals

record ProjectivePlane (P L : Set) : Set (lsuc lzero) where
  field
    incident : P -> L -> Set
    join     : P -> P -> L
    meet     : L -> L -> P

    join-left :
      (a b : P) ->
      incident a (join a b)
    join-right :
      (a b : P) ->
      incident b (join a b)
    meet-left :
      (l m : L) ->
      incident (meet l m) l
    meet-right :
      (l m : L) ->
      incident (meet l m) m

    join-unique :
      (a b : P) ->
      a != b ->
      (l : L) ->
      incident a l ->
      incident b l ->
      l == join a b
    meet-unique :
      (l m : L) ->
      l != m ->
      (p : P) ->
      incident p l ->
      incident p m ->
      p == meet l m

    noncollinear-points :
      Exists P
        (\ a ->
          Exists P
            (\ b ->
              Exists P
                (\ c ->
                  a != b and
                  b != c and
                  a != c and
                  Not
                    (Exists L
                      (\ l ->
                        incident a l and
                        incident b l and
                        incident c l)))))

    three-points-on-line :
      (l : L) ->
      Exists P
        (\ a ->
          Exists P
            (\ b ->
              Exists P
                (\ c ->
                  a != b and
                  b != c and
                  a != c and
                  incident a l and
                  incident b l and
                  incident c l)))

open ProjectivePlane

ProjectiveCollinear :
  {P L : Set} ->
  ProjectivePlane P L ->
  P ->
  P ->
  P ->
  Set
ProjectiveCollinear plane a b c =
  Exists _
    (\ l ->
      incident plane a l and
      incident plane b l and
      incident plane c l)

DistinctSix :
  {A : Set} ->
  A ->
  A ->
  A ->
  A ->
  A ->
  A ->
  Set
DistinctSix a b c d e f =
  a != b and
  a != c and
  a != d and
  a != e and
  a != f and
  b != c and
  b != d and
  b != e and
  b != f and
  c != d and
  c != e and
  c != f and
  d != e and
  d != f and
  e != f

OnIntersection :
  {P L : Set} ->
  ProjectivePlane P L ->
  P ->
  P ->
  P ->
  P ->
  P ->
  Set
OnIntersection plane p a b c d =
  ProjectiveCollinear plane p a b and
  ProjectiveCollinear plane p c d

HexamyConfiguration :
  {P L : Set} ->
  ProjectivePlane P L ->
  P ->
  P ->
  P ->
  P ->
  P ->
  P ->
  Set
HexamyConfiguration plane a b c d e f =
  DistinctSix a b c d e f and
  ProjectiveCollinear plane
    (meet plane (join plane b c) (join plane e f))
    (meet plane (join plane c d) (join plane f a))
    (meet plane (join plane a b) (join plane d e))

HexamyProperty :
  {P L : Set} ->
  ProjectivePlane P L ->
  Set
HexamyProperty {P} plane =
  (a b c d e f : P) ->
  HexamyConfiguration plane a b c d e f ->
  HexamyConfiguration plane b a c d e f

PappusRegular :
  {P L : Set} ->
  ProjectivePlane P L ->
  P ->
  P ->
  P ->
  P ->
  P ->
  P ->
  Set
PappusRegular plane a b c a-prime b-prime c-prime =
  join plane a b-prime != join plane a-prime b and
  a != b-prime and
  a-prime != b and
  join plane b c-prime != join plane b-prime c and
  b != c-prime and
  b-prime != c and
  join plane a c-prime != join plane a-prime c and
  a != c-prime and
  a-prime != c

PappusStrong :
  {P L : Set} ->
  ProjectivePlane P L ->
  Set
PappusStrong {P} plane =
  (a b c a-prime b-prime c-prime p q r : P) ->
  (DistinctSix a b c a-prime b-prime c-prime or
   PappusRegular plane a b c a-prime b-prime c-prime) ->
  ProjectiveCollinear plane a b c ->
  ProjectiveCollinear plane a-prime b-prime c-prime ->
  OnIntersection plane p a b-prime a-prime b ->
  OnIntersection plane q b c-prime b-prime c ->
  OnIntersection plane r a c-prime a-prime c ->
  ProjectiveCollinear plane p q r

PappusImpliesHexamy :
  {P L : Set} ->
  ProjectivePlane P L ->
  Set
PappusImpliesHexamy {P} plane =
  PappusStrong plane ->
  (a b c d e f : P) ->
  join plane c d != join plane a f ->
  join plane b c != join plane e f ->
  join plane a b != join plane d e ->
  join plane a c != join plane e f ->
  join plane b f != join plane c d ->
  HexamyConfiguration plane a b c d e f ->
  HexamyConfiguration plane b a c d e f

rocq-pappus-implies-hexamy : Set (lsuc lzero)
rocq-pappus-implies-hexamy =
  (P L : Set) ->
  (plane : ProjectivePlane P L) ->
  PappusImpliesHexamy plane
