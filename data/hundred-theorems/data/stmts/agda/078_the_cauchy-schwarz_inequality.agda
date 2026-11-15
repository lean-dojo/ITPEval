-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__078,
-- "The Cauchy-Schwarz Inequality": in every real inner product space, the absolute
-- value of an inner product is at most the product of the two norms. This file contains no proof.

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_

data Bottom : Set where

Not : ∀ {l} -> Set l -> Set l
Not A = A -> Bottom

_!=_ : ∀ {l} {A : Set l} -> A -> A -> Set l
x != y = Not (x == y)

record Both {l1 l2 : Level} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2) where
  constructor both
  field
    first  : A
    second : B

data Either {l1 l2 : Level} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2) where
  left  : A -> Either A B
  right : B -> Either A B

record Exists {l1 l2 : Level} (A : Set l1) (P : A -> Set l2) :
    Set (l1 ⊔ l2) where
  constructor witness
  field
    value    : A
    property : P value

record CompleteOrderedRealField {l : Level} (R : Set l) : Set (lsuc l) where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR absoluteValueR squareRootR : R -> R
    lessOrEqualR : R -> R -> Set l
    fromNatR : Nat -> R

    oneR-not-zeroR :
      oneR != zeroR

    addR-commutative :
      (x y : R) -> addR x y == addR y x
    addR-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    addR-zero :
      (x : R) -> addR x zeroR == x
    addR-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiplyR-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiplyR-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiplyR-one :
      (x : R) -> multiplyR x oneR == x
    multiplyR-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverseR-zero :
      inverseR zeroR == zeroR
    multiplyR-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
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
    addR-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiplyR-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zeroR-less-than-oneR :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    fromNatR-zero :
      fromNatR zero == zeroR
    fromNatR-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNatR-addition :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNatR-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNatR-injective :
      (m n : Nat) -> fromNatR m == fromNatR n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))

    least-upper-bound :
      (P : R -> Set l) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

    absolute-value-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR (absoluteValueR x)
    absolute-value-upper :
      (x : R) ->
      Both
        (lessOrEqualR x (absoluteValueR x))
        (lessOrEqualR (negateR x) (absoluteValueR x))
    absolute-value-least :
      (x upper : R) ->
      lessOrEqualR x upper ->
      lessOrEqualR (negateR x) upper ->
      lessOrEqualR (absoluteValueR x) upper

    square-root-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR (squareRootR x)
    square-root-square :
      (x : R) ->
      lessOrEqualR zeroR x ->
      multiplyR (squareRootR x) (squareRootR x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqualR x zeroR ->
      squareRootR x == zeroR
    square-root-unique :
      (x y : R) ->
      lessOrEqualR zeroR y ->
      multiplyR y y == x ->
      y == squareRootR x

open CompleteOrderedRealField

record RealInnerProductSpace
    {lR lV : Level}
    (R : Set lR)
    (reals : CompleteOrderedRealField R)
    (V : Set lV) :
    Set (lsuc (lR ⊔ lV)) where
  field
    zeroV : V
    addV : V -> V -> V
    negateV : V -> V
    scaleV : R -> V -> V
    innerProduct : V -> V -> R

    addV-commutative :
      (u v : V) -> addV u v == addV v u
    addV-associative :
      (u v w : V) -> addV (addV u v) w == addV u (addV v w)
    addV-zero :
      (u : V) -> addV u zeroV == u
    addV-inverse :
      (u : V) -> addV u (negateV u) == zeroV

    scaleV-one :
      (u : V) -> scaleV (oneR reals) u == u
    scaleV-associative :
      (a b : R) ->
      (u : V) ->
      scaleV (multiplyR reals a b) u == scaleV a (scaleV b u)
    scaleV-add-scalars :
      (a b : R) ->
      (u : V) ->
      scaleV (addR reals a b) u == addV (scaleV a u) (scaleV b u)
    scaleV-add-vectors :
      (a : R) ->
      (u v : V) ->
      scaleV a (addV u v) == addV (scaleV a u) (scaleV a v)

    inner-symmetric :
      (u v : V) -> innerProduct u v == innerProduct v u
    inner-add-left :
      (u v w : V) ->
      innerProduct (addV u v) w ==
      addR reals (innerProduct u w) (innerProduct v w)
    inner-scale-left :
      (a : R) ->
      (u v : V) ->
      innerProduct (scaleV a u) v ==
      multiplyR reals a (innerProduct u v)
    inner-nonnegative :
      (u : V) ->
      lessOrEqualR reals (zeroR reals) (innerProduct u u)
    inner-definite :
      (u : V) ->
      innerProduct u u == zeroR reals ->
      u == zeroV

open RealInnerProductSpace

norm :
  ∀ {lR lV}
  {R : Set lR} ->
  (reals : CompleteOrderedRealField R) ->
  {V : Set lV} ->
  RealInnerProductSpace R reals V ->
  V ->
  R
norm reals space u =
  squareRootR reals (innerProduct space u u)

the-cauchy-schwarz-inequality : Setω
the-cauchy-schwarz-inequality =
  ∀ {lR lV} ->
  (R : Set lR) ->
  (reals : CompleteOrderedRealField R) ->
  (V : Set lV) ->
  (space : RealInnerProductSpace R reals V) ->
  (u v : V) ->
  lessOrEqualR reals
    (absoluteValueR reals (innerProduct space u v))
    (multiplyR reals
      (norm reals space u)
      (norm reals space v))
