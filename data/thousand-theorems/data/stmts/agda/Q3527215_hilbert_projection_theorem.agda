-- Statement-only formalization of thousand-theorems corpus artifact Q3527215,
-- "Hilbert projection theorem": every point in a real inner-product space has a
-- distance-minimizing point in each nonempty complete convex subset. This file contains no proof.

{-# OPTIONS --safe #-}

module Q3527215_hilbert_projection_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) -> addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) -> addR x zeroR == x
    add-inverseR :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) -> multiplyR x oneR == x
    multiply-zeroR :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexiveR :
      (x : R) -> lessOrEqualR x x
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
      (x y : R) -> Either (lessOrEqualR x y) (lessOrEqualR y x)
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
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-injectiveR :
      (m n : Nat) -> fromNatR m == fromNatR n -> m == n

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set) ->
      Exists R P ->
      Exists R (\ upper -> (x : R) -> P x -> lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

record RealInnerProductSpace
  (R F : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroF : F
    addF : F -> F -> F
    negateF : F -> F
    scaleF : R -> F -> F
    innerF : F -> F -> R
    normF : F -> R

    add-commutativeF :
      (x y : F) -> addF x y == addF y x
    add-associativeF :
      (x y z : F) ->
      addF (addF x y) z == addF x (addF y z)
    add-zeroF :
      (x : F) -> addF x zeroF == x
    add-inverseF :
      (x : F) -> addF x (negateF x) == zeroF

    scale-oneF :
      (x : F) -> scaleF (oneR reals) x == x
    scale-associativeF :
      (a b : R) ->
      (x : F) ->
      scaleF (multiplyR reals a b) x == scaleF a (scaleF b x)
    scale-add-vectorsF :
      (a : R) ->
      (x y : F) ->
      scaleF a (addF x y) == addF (scaleF a x) (scaleF a y)
    scale-add-scalarsF :
      (a b : R) ->
      (x : F) ->
      scaleF (addR reals a b) x == addF (scaleF a x) (scaleF b x)

    inner-add-leftF :
      (x y z : F) ->
      innerF (addF x y) z ==
      addR reals (innerF x z) (innerF y z)
    inner-scale-leftF :
      (a : R) ->
      (x y : F) ->
      innerF (scaleF a x) y ==
      multiplyR reals a (innerF x y)
    inner-symmetricF :
      (x y : F) -> innerF x y == innerF y x
    inner-nonnegativeF :
      (x : F) ->
      lessOrEqualR reals (zeroR reals) (innerF x x)
    inner-definiteF :
      (x : F) ->
      innerF x x == zeroR reals ->
      x == zeroF

    norm-nonnegativeF :
      (x : F) ->
      lessOrEqualR reals (zeroR reals) (normF x)
    norm-squareF :
      (x : F) ->
      multiplyR reals (normF x) (normF x) == innerF x x

open RealInnerProductSpace

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

subtractF :
  {R F : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace R F reals ->
  F ->
  F ->
  F
subtractF space x y =
  addF space x (negateF space y)

distanceF :
  {R F : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace R F reals ->
  F ->
  F ->
  R
distanceF space x y =
  normF space (subtractF space x y)

SequentialLimit :
  {R F : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace R F reals ->
  (Nat -> F) ->
  F ->
  Set
SequentialLimit {R = R} {reals = reals} space sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals (distanceF space (sequence n) limit) epsilon)

CauchySequence :
  {R F : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace R F reals ->
  (Nat -> F) ->
  Set
CauchySequence {R = R} {reals = reals} space sequence =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <=N m ->
      cutoff <=N n ->
      StrictLess reals
        (distanceF space (sequence m) (sequence n))
        epsilon)

Nonempty :
  {F : Set} ->
  (F -> Set) ->
  Set
Nonempty {F} K =
  Exists F K

IsComplete :
  {R F : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace R F reals ->
  (F -> Set) ->
  Set
IsComplete {F = F} space K =
  (sequence : Nat -> F) ->
  ((n : Nat) -> K (sequence n)) ->
  CauchySequence space sequence ->
  Exists F
    (\ limit ->
      Both
        (K limit)
        (SequentialLimit space sequence limit))

Convex :
  {R F : Set} ->
  (reals : CompleteOrderedField R) ->
  RealInnerProductSpace R F reals ->
  (F -> Set) ->
  Set
Convex {R = R} {F = F} reals space K =
  (x y : F) ->
  K x ->
  K y ->
  (t : R) ->
  lessOrEqualR reals (zeroR reals) t ->
  lessOrEqualR reals t (oneR reals) ->
  K
    (addF space
      (scaleF space t x)
      (scaleF space (subtractR reals (oneR reals) t) y))

IsInfimumDistance :
  {R F : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace R F reals ->
  F ->
  (F -> Set) ->
  R ->
  Set
IsInfimumDistance {R = R} {F = F} {reals = reals} space u K infimum =
  Both
    ((w : F) -> K w -> lessOrEqualR reals infimum (distanceF space u w))
    ((lower : R) ->
      ((w : F) -> K w -> lessOrEqualR reals lower (distanceF space u w)) ->
      lessOrEqualR reals lower infimum)

hilbert-projection-theorem : Set1
hilbert-projection-theorem =
  (R F : Set) ->
  (reals : CompleteOrderedField R) ->
  (space : RealInnerProductSpace R F reals) ->
  (K : F -> Set) ->
  Nonempty K ->
  IsComplete space K ->
  Convex reals space K ->
  (u : F) ->
  Exists F
    (\ v ->
      Both
        (K v)
        (IsInfimumDistance space u K (distanceF space u v)))
