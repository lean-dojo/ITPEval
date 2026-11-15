-- Statement-only formalization of thousand-theorems corpus artifact Q3527217,
-- "M. Riesz extension theorem": a real-linear functional on a subspace that is
-- nonnegative on a pointed cone extends to a global real-linear functional
-- nonnegative on that cone under the stated cone-generation condition.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q3527217_m_riesz_extension_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

record CompleteOrderedField
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

    negateR reciprocalR :
      R ->
      R

    lessOrEqualR :
      R ->
      R ->
      Set r

    fromNatR :
      Nat ->
      R

    order-propositionalR :
      (x y : R) ->
      (left-proof right-proof : lessOrEqualR x y) ->
      left-proof == right-proof

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
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)

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

    reciprocal-zeroR :
      reciprocalR zeroR == zeroR

    multiply-reciprocalR :
      (x : R) ->
      Not (x == zeroR) ->
      multiplyR x (reciprocalR x) == oneR

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
      Either
        (lessOrEqualR x y)
        (lessOrEqualR y x)

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
      Both
        (lessOrEqualR zeroR oneR)
        (Not (zeroR == oneR))

    fromNat-zeroR :
      fromNatR zero == zeroR

    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR

    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat
        (\ n -> lessOrEqualR x (fromNatR n))

    least-upper-boundR :
      (P : R -> Set r) ->
      ((x : R) -> (p q : P x) -> p == q) ->
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

record RealVectorSpace
  {r e : Level}
  {R : Set r}
  (reals : CompleteOrderedField R)
  (E : Set e) :
  Set (lsuc (r ⊔ e)) where

  open CompleteOrderedField reals

  field
    zeroV :
      E

    addV :
      E ->
      E ->
      E

    negateV :
      E ->
      E

    scaleV :
      R ->
      E ->
      E

    add-commutativeV :
      (x y : E) ->
      addV x y == addV y x

    add-associativeV :
      (x y z : E) ->
      addV (addV x y) z == addV x (addV y z)

    add-zeroV :
      (x : E) ->
      addV x zeroV == x

    add-inverseV :
      (x : E) ->
      addV x (negateV x) == zeroV

    scale-oneV :
      (x : E) ->
      scaleV oneR x == x

    scale-associativeV :
      (a b : R) ->
      (x : E) ->
      scaleV (multiplyR a b) x == scaleV a (scaleV b x)

    scale-add-vectorsV :
      (a : R) ->
      (x y : E) ->
      scaleV a (addV x y) == addV (scaleV a x) (scaleV a y)

    scale-add-scalarsV :
      (a b : R) ->
      (x : E) ->
      scaleV (addR a b) x == addV (scaleV a x) (scaleV b x)

record Subspace
  {r e : Level}
  {R : Set r}
  {E : Set e}
  (reals : CompleteOrderedField R)
  (space : RealVectorSpace reals E) :
  Set (lsuc (r ⊔ e)) where

  open CompleteOrderedField reals
  open RealVectorSpace space

  field
    memberS :
      E ->
      Set e

    member-propositionalS :
      (x : E) ->
      (left-proof right-proof : memberS x) ->
      left-proof == right-proof

    zero-memberS :
      memberS zeroV

    add-memberS :
      (x y : E) ->
      memberS x ->
      memberS y ->
      memberS (addV x y)

    scale-memberS :
      (a : R) ->
      (x : E) ->
      memberS x ->
      memberS (scaleV a x)

record PointedCone
  {r e : Level}
  {R : Set r}
  {E : Set e}
  (reals : CompleteOrderedField R)
  (space : RealVectorSpace reals E) :
  Set (lsuc (r ⊔ e)) where

  open CompleteOrderedField reals
  open RealVectorSpace space

  field
    memberC :
      E ->
      Set e

    member-propositionalC :
      (x : E) ->
      (left-proof right-proof : memberC x) ->
      left-proof == right-proof

    zero-memberC :
      memberC zeroV

    add-memberC :
      (x y : E) ->
      memberC x ->
      memberC y ->
      memberC (addV x y)

    nonnegative-scale-memberC :
      (a : R) ->
      lessOrEqualR zeroR a ->
      (x : E) ->
      memberC x ->
      memberC (scaleV a x)

record PartialLinearFunctional
  {r e : Level}
  {R : Set r}
  {E : Set e}
  (reals : CompleteOrderedField R)
  (space : RealVectorSpace reals E) :
  Set (lsuc (r ⊔ e)) where

  open CompleteOrderedField reals
  open RealVectorSpace space

  field
    domain :
      Subspace reals space

    applyP :
      (x : E) ->
      Subspace.memberS domain x ->
      R

    apply-proof-independentP :
      (x : E) ->
      (left-proof right-proof : Subspace.memberS domain x) ->
      applyP x left-proof == applyP x right-proof

    map-zeroP :
      applyP zeroV (Subspace.zero-memberS domain) == zeroR

    map-addP :
      (x y : E) ->
      (x-member : Subspace.memberS domain x) ->
      (y-member : Subspace.memberS domain y) ->
      applyP
        (addV x y)
        (Subspace.add-memberS domain x y x-member y-member)
      ==
      addR (applyP x x-member) (applyP y y-member)

    map-scaleP :
      (a : R) ->
      (x : E) ->
      (x-member : Subspace.memberS domain x) ->
      applyP
        (scaleV a x)
        (Subspace.scale-memberS domain a x x-member)
      ==
      multiplyR a (applyP x x-member)

record GlobalLinearFunctional
  {r e : Level}
  {R : Set r}
  {E : Set e}
  (reals : CompleteOrderedField R)
  (space : RealVectorSpace reals E) :
  Set (lsuc (r ⊔ e)) where

  open CompleteOrderedField reals
  open RealVectorSpace space

  field
    applyG :
      E ->
      R

    map-zeroG :
      applyG zeroV == zeroR

    map-addG :
      (x y : E) ->
      applyG (addV x y) == addR (applyG x) (applyG y)

    map-scaleG :
      (a : R) ->
      (x : E) ->
      applyG (scaleV a x) == multiplyR a (applyG x)

m-riesz-extension-theorem :
  (r e : Level) ->
  Set (lsuc (r ⊔ e))
m-riesz-extension-theorem r e =
  (R : Set r) ->
  (reals : CompleteOrderedField R) ->
  (E : Set e) ->
  (space : RealVectorSpace reals E) ->
  (cone : PointedCone reals space) ->
  (f : PartialLinearFunctional reals space) ->
  ((x : E) ->
    (x-member : Subspace.memberS (PartialLinearFunctional.domain f) x) ->
    PointedCone.memberC cone x ->
    CompleteOrderedField.lessOrEqualR reals
      (CompleteOrderedField.zeroR reals)
      (PartialLinearFunctional.applyP f x x-member)) ->
  ((y : E) ->
    Exists E
      (\ x ->
        Both
          (Subspace.memberS (PartialLinearFunctional.domain f) x)
          (PointedCone.memberC cone
            (RealVectorSpace.addV space x y)))) ->
  Exists
    (GlobalLinearFunctional reals space)
    (\ g ->
      Both
        ((x : E) ->
          (x-member : Subspace.memberS
            (PartialLinearFunctional.domain f) x) ->
          GlobalLinearFunctional.applyG g x ==
          PartialLinearFunctional.applyP f x x-member)
        ((x : E) ->
          PointedCone.memberC cone x ->
          CompleteOrderedField.lessOrEqualR reals
            (CompleteOrderedField.zeroR reals)
            (GlobalLinearFunctional.applyG g x)))
