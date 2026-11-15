-- Statement-only formalization of thousand-theorems corpus artifact Q3527205,
-- "Dimension theorem for vector spaces": over a semiring with invariant basis
-- number, any two bases of the same module have equipotent index types. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module Q3527205_dimension_theorem_for_vector_spaces where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} A =
  A -> Bottom {a}

data Fin : Nat -> Set where
  first : {n : Nat} -> Fin (suc n)
  next  : {n : Nat} -> Fin n -> Fin (suc n)

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    forward :
      A -> B
    backward :
      B -> A
    backward-forward :
      (x : A) ->
      backward (forward x) == x
    forward-backward :
      (y : B) ->
      forward (backward y) == y

record Semiring
  {r : Level}
  (R : Set r) :
  Set r where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R

    add-associative :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-commutative :
      (x y : R) ->
      addR x y == addR y x
    add-zero-left :
      (x : R) ->
      addR zeroR x == x
    add-zero-right :
      (x : R) ->
      addR x zeroR == x

    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-one-left :
      (x : R) ->
      multiplyR oneR x == x
    multiply-one-right :
      (x : R) ->
      multiplyR x oneR == x
    multiply-zero-left :
      (x : R) ->
      multiplyR zeroR x == zeroR
    multiply-zero-right :
      (x : R) ->
      multiplyR x zeroR == zeroR
    distribute-left :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : R) ->
      multiplyR (addR x y) z ==
      addR (multiplyR x z) (multiplyR y z)

record AdditiveCommutativeMonoid
  {m : Level}
  (M : Set m) :
  Set m where

  field
    zeroM : M
    addM : M -> M -> M

    add-associative :
      (x y z : M) ->
      addM (addM x y) z == addM x (addM y z)
    add-commutative :
      (x y : M) ->
      addM x y == addM y x
    add-zero-left :
      (x : M) ->
      addM zeroM x == x
    add-zero-right :
      (x : M) ->
      addM x zeroM == x

record Module
  {r m : Level}
  {R : Set r}
  {M : Set m}
  (ring : Semiring R)
  (additive : AdditiveCommutativeMonoid M) :
  Set (r ⊔ m) where

  field
    scale :
      R -> M -> M
    one-scale :
      (x : M) ->
      scale (Semiring.oneR ring) x == x
    multiply-scale :
      (a b : R) (x : M) ->
      scale (Semiring.multiplyR ring a b) x ==
      scale a (scale b x)
    add-scale :
      (a b : R) (x : M) ->
      scale (Semiring.addR ring a b) x ==
      AdditiveCommutativeMonoid.addM additive
        (scale a x)
        (scale b x)
    scale-add :
      (a : R) (x y : M) ->
      scale a (AdditiveCommutativeMonoid.addM additive x y) ==
      AdditiveCommutativeMonoid.addM additive
        (scale a x)
        (scale a y)
    zero-scale :
      (x : M) ->
      scale (Semiring.zeroR ring) x ==
      AdditiveCommutativeMonoid.zeroM additive
    scale-zero :
      (a : R) ->
      scale a (AdditiveCommutativeMonoid.zeroM additive) ==
      AdditiveCommutativeMonoid.zeroM additive

record FiniteCoefficients
  {r i : Level}
  (I : Set i)
  (R : Set r)
  (ring : Semiring R) :
  Set (r ⊔ i) where

  field
    value :
      I -> R
    support-size :
      Nat
    support :
      Fin support-size -> I
    zero-outside-support :
      (index : I) ->
      Not
        (Σ (Fin support-size)
          (\ position -> support position == index)) ->
      value index == Semiring.zeroR ring

CoefficientsEqual :
  {r i : Level} ->
  {R : Set r} ->
  {I : Set i} ->
  {ring : Semiring R} ->
  FiniteCoefficients I R ring ->
  FiniteCoefficients I R ring ->
  Set (r ⊔ i)
CoefficientsEqual {I = I} left right =
  (index : I) ->
  FiniteCoefficients.value left index ==
  FiniteCoefficients.value right index

record Basis
  {r m i : Level}
  {R : Set r}
  {M : Set m}
  (I : Set i)
  (ring : Semiring R)
  (additive : AdditiveCommutativeMonoid M)
  (module-structure : Module ring additive) :
  Set (r ⊔ m ⊔ i) where

  field
    coordinates :
      M -> FiniteCoefficients I R ring
    rebuild :
      FiniteCoefficients I R ring -> M
    coordinates-after-rebuild :
      (coefficients : FiniteCoefficients I R ring) ->
      CoefficientsEqual
        (coordinates (rebuild coefficients))
        coefficients
    rebuild-after-coordinates :
      (x : M) ->
      rebuild (coordinates x) == x
    rebuild-congruent :
      (left right : FiniteCoefficients I R ring) ->
      CoefficientsEqual left right ->
      rebuild left == rebuild right
    coordinates-add :
      (x y : M) ->
      (index : I) ->
      FiniteCoefficients.value
        (coordinates
          (AdditiveCommutativeMonoid.addM additive x y))
        index ==
      Semiring.addR ring
        (FiniteCoefficients.value (coordinates x) index)
        (FiniteCoefficients.value (coordinates y) index)
    coordinates-scale :
      (scalar : R) ->
      (x : M) ->
      (index : I) ->
      FiniteCoefficients.value
        (coordinates (Module.scale module-structure scalar x))
        index ==
      Semiring.multiplyR ring scalar
        (FiniteCoefficients.value (coordinates x) index)

PointwiseEqual :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (A -> B) ->
  (A -> B) ->
  Set (a ⊔ b)
PointwiseEqual {A = A} f g =
  (x : A) -> f x == g x

PowerVector :
  {r : Level} ->
  Set r ->
  Nat ->
  Set r
PowerVector R n =
  Fin n -> R

record PowerLinearEquivalence
  {r : Level}
  {R : Set r}
  (ring : Semiring R)
  (n m : Nat) :
  Set r where

  field
    forward :
      PowerVector R n -> PowerVector R m
    backward :
      PowerVector R m -> PowerVector R n
    forward-congruent :
      (x y : PowerVector R n) ->
      PointwiseEqual x y ->
      PointwiseEqual (forward x) (forward y)
    backward-congruent :
      (x y : PowerVector R m) ->
      PointwiseEqual x y ->
      PointwiseEqual (backward x) (backward y)
    backward-forward :
      (x : PowerVector R n) ->
      PointwiseEqual (backward (forward x)) x
    forward-backward :
      (y : PowerVector R m) ->
      PointwiseEqual (forward (backward y)) y
    forward-add :
      (x y : PowerVector R n) ->
      PointwiseEqual
        (forward
          (\ i -> Semiring.addR ring (x i) (y i)))
        (\ j ->
          Semiring.addR ring (forward x j) (forward y j))
    forward-scale :
      (a : R) ->
      (x : PowerVector R n) ->
      PointwiseEqual
        (forward
          (\ i -> Semiring.multiplyR ring a (x i)))
        (\ j ->
          Semiring.multiplyR ring a (forward x j))

record InvariantBasisNumber
  {r : Level}
  {R : Set r}
  (ring : Semiring R) :
  Set r where

  field
    finite-free-ranks-unique :
      (n m : Nat) ->
      PowerLinearEquivalence ring n m ->
      n == m

dimension-theorem-for-vector-spaces : Setω
dimension-theorem-for-vector-spaces =
  {r m i j : Level} ->
  (R : Set r) ->
  (M : Set m) ->
  (ring : Semiring R) ->
  (additive : AdditiveCommutativeMonoid M) ->
  (module-structure : Module ring additive) ->
  InvariantBasisNumber ring ->
  (I : Set i) ->
  (J : Set j) ->
  (first-basis : Basis I ring additive module-structure) ->
  (second-basis : Basis J ring additive module-structure) ->
  Bijection I J
