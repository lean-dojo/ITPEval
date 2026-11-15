-- Statement-only formalization of thousand-theorems corpus artifact Q739403
-- (thousand-theorems__agda__Q739403), "Stewart's theorem": in a real
-- inner-product affine space, a straight angle at a point on a line gives
-- Stewart's distance identity. This file contains no proof.

{-# OPTIONS --safe #-}

module Q739403_stewart_s_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

data Bottom {a : Level} : Set a where

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

record Exists
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

  constructor witness
  field
    value    : A
    property : P value

record CompleteOrderedRealField
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set r
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) ->
      addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) ->
      addR x zeroR == x
    add-inverseR :
      (x : R) ->
      addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) ->
      multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) ->
      multiplyR x oneR == x
    multiply-zeroR :
      (x : R) ->
      multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverse-zeroR :
      inverseR zeroR == zeroR
    multiply-inverseR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

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

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
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

open CompleteOrderedRealField

record RealInnerProductSpace
  {r v : Level}
  {R : Set r}
  (reals : CompleteOrderedRealField R)
  (V : Set v) :
  Set (lsuc (r ⊔ v)) where

  field
    zeroV : V
    addV : V -> V -> V
    negateV : V -> V
    scaleV : R -> V -> V

    addV-commutative :
      (u w : V) ->
      addV u w == addV w u
    addV-associative :
      (u w z : V) ->
      addV (addV u w) z == addV u (addV w z)
    addV-zero :
      (u : V) ->
      addV u zeroV == u
    addV-inverse :
      (u : V) ->
      addV u (negateV u) == zeroV

    scale-addV :
      (a : R) ->
      (u w : V) ->
      scaleV a (addV u w) ==
      addV (scaleV a u) (scaleV a w)
    add-scaleV :
      (a b : R) ->
      (u : V) ->
      scaleV (addR reals a b) u ==
      addV (scaleV a u) (scaleV b u)
    multiply-scaleV :
      (a b : R) ->
      (u : V) ->
      scaleV (multiplyR reals a b) u ==
      scaleV a (scaleV b u)
    one-scaleV :
      (u : V) ->
      scaleV (oneR reals) u == u

    inner : V -> V -> R
    inner-add-left :
      (u w z : V) ->
      inner (addV u w) z ==
      addR reals (inner u z) (inner w z)
    inner-scale-left :
      (a : R) ->
      (u w : V) ->
      inner (scaleV a u) w ==
      multiplyR reals a (inner u w)
    inner-symmetric :
      (u w : V) ->
      inner u w == inner w u
    inner-nonnegative :
      (u : V) ->
      lessOrEqualR reals (zeroR reals) (inner u u)
    inner-definite :
      (u : V) ->
      inner u u == zeroR reals ->
      u == zeroV

    norm : V -> R
    norm-nonnegative :
      (u : V) ->
      lessOrEqualR reals (zeroR reals) (norm u)
    norm-square :
      (u : V) ->
      multiplyR reals (norm u) (norm u) == inner u u
    norm-zero :
      (u : V) ->
      norm u == zeroR reals ->
      u == zeroV
    norm-negate :
      (u : V) ->
      norm (negateV u) == norm u

open RealInnerProductSpace

record AffineTorsor
  {r v p : Level}
  {R : Set r}
  {V : Set v}
  {reals : CompleteOrderedRealField R}
  (space : RealInnerProductSpace reals V)
  (P : Set p) :
  Set (lsuc (r ⊔ v ⊔ p)) where

  field
    vadd : V -> P -> P
    vsub : P -> P -> V

    zero-vadd :
      (x : P) ->
      vadd (zeroV space) x == x
    add-vadd :
      (u w : V) ->
      (x : P) ->
      vadd (addV space u w) x ==
      vadd u (vadd w x)
    vadd-vsub :
      (x y : P) ->
      vadd (vsub x y) y == x
    vsub-vadd :
      (u : V) ->
      (x : P) ->
      vsub (vadd u x) x == u

open AffineTorsor

square :
  {r : Level} ->
  {R : Set r} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiplyR reals x x

distance :
  {r v p : Level} ->
  {R : Set r} ->
  {V : Set v} ->
  {P : Set p} ->
  {reals : CompleteOrderedRealField R} ->
  {space : RealInnerProductSpace reals V} ->
  AffineTorsor space P ->
  P ->
  P ->
  R
distance {space = space} affine x y =
  norm space (vsub affine x y)

StraightAngleAt :
  {r v p : Level} ->
  {R : Set r} ->
  {V : Set v} ->
  {P : Set p} ->
  (reals : CompleteOrderedRealField R) ->
  (space : RealInnerProductSpace reals V) ->
  AffineTorsor space P ->
  P ->
  P ->
  P ->
  Set (r ⊔ v)
StraightAngleAt reals space affine b p c =
  Both
    (vsub affine b p != zeroV space)
    (Both
      (vsub affine c p != zeroV space)
      (inner space (vsub affine b p) (vsub affine c p) ==
       negateR reals
         (multiplyR reals
           (norm space (vsub affine b p))
           (norm space (vsub affine c p)))))

stewart-theorem : Setω
stewart-theorem =
  {r v p : Level} ->
  (R : Set r) ->
  (V : Set v) ->
  (P : Set p) ->
  (reals : CompleteOrderedRealField R) ->
  (space : RealInnerProductSpace reals V) ->
  (affine : AffineTorsor space P) ->
  (a b c point : P) ->
  StraightAngleAt reals space affine b point c ->
  addR reals
    (multiplyR reals
      (square reals (distance affine a b))
      (distance affine c point))
    (multiplyR reals
      (square reals (distance affine a c))
      (distance affine b point))
  ==
  multiplyR reals
    (distance affine b c)
    (addR reals
      (square reals (distance affine a point))
      (multiplyR reals
        (distance affine b point)
        (distance affine c point)))
