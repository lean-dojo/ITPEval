-- Statement-only formalization of Thousand Theorems corpus artifact Q2226625,
-- "Commandino's theorem": in a positive-dimensional simplex, the vector from
-- a vertex to the centroid is the dimension times the vector from the centroid
-- to the centroid of the opposite face. This file contains no proof.

{-# OPTIONS --safe #-}

module Q2226625_commandino_s_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} A =
  A -> Bottom {a}

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

foldFin :
  {a : Level} ->
  {A : Set a} ->
  A ->
  (A -> A -> A) ->
  {n : Nat} ->
  (Fin n -> A) ->
  A
foldFin neutral combine {zero} values =
  neutral
foldFin neutral combine {suc n} values =
  combine
    (values fzero)
    (foldFin neutral combine (\ i -> values (fsuc i)))

record DivisionRing
  {k : Level}
  (K : Set k) :
  Set k where

  field
    zeroK oneK : K
    addK multiplyK : K -> K -> K
    negateK inverseK : K -> K

    one-not-zeroK :
      oneK != zeroK

    add-associativeK :
      (x y z : K) ->
      addK (addK x y) z == addK x (addK y z)
    add-commutativeK :
      (x y : K) ->
      addK x y == addK y x
    add-zero-leftK :
      (x : K) ->
      addK zeroK x == x
    add-inverse-leftK :
      (x : K) ->
      addK (negateK x) x == zeroK

    multiply-associativeK :
      (x y z : K) ->
      multiplyK (multiplyK x y) z ==
      multiplyK x (multiplyK y z)
    multiply-one-leftK :
      (x : K) ->
      multiplyK oneK x == x
    multiply-one-rightK :
      (x : K) ->
      multiplyK x oneK == x
    multiply-zero-leftK :
      (x : K) ->
      multiplyK zeroK x == zeroK
    multiply-zero-rightK :
      (x : K) ->
      multiplyK x zeroK == zeroK

    distribute-leftK :
      (x y z : K) ->
      multiplyK x (addK y z) ==
      addK (multiplyK x y) (multiplyK x z)
    distribute-rightK :
      (x y z : K) ->
      multiplyK (addK x y) z ==
      addK (multiplyK x z) (multiplyK y z)

    inverse-zeroK :
      inverseK zeroK == zeroK
    multiply-inverseK :
      (x : K) ->
      x != zeroK ->
      multiplyK x (inverseK x) == oneK
    inverse-multiplyK :
      (x : K) ->
      x != zeroK ->
      multiplyK (inverseK x) x == oneK

open DivisionRing

natCast :
  {k : Level} ->
  {K : Set k} ->
  DivisionRing K ->
  Nat ->
  K
natCast ring zero =
  zeroK ring
natCast ring (suc n) =
  addK ring (natCast ring n) (oneK ring)

CharZero :
  {k : Level} ->
  {K : Set k} ->
  DivisionRing K ->
  Set k
CharZero ring =
  (m n : Nat) ->
  natCast ring m == natCast ring n ->
  m == n

sumK :
  {k : Level} ->
  {K : Set k} ->
  (ring : DivisionRing K) ->
  {n : Nat} ->
  (Fin n -> K) ->
  K
sumK ring =
  foldFin (zeroK ring) (addK ring)

record AdditiveCommutativeGroup
  {v : Level}
  (V : Set v) :
  Set v where

  field
    zeroV : V
    addV : V -> V -> V
    negateV : V -> V

    add-associativeV :
      (x y z : V) ->
      addV (addV x y) z == addV x (addV y z)
    add-commutativeV :
      (x y : V) ->
      addV x y == addV y x
    add-zero-leftV :
      (x : V) ->
      addV zeroV x == x
    add-inverse-leftV :
      (x : V) ->
      addV (negateV x) x == zeroV

open AdditiveCommutativeGroup

sumV :
  {v : Level} ->
  {V : Set v} ->
  (vectors : AdditiveCommutativeGroup V) ->
  {n : Nat} ->
  (Fin n -> V) ->
  V
sumV vectors =
  foldFin (zeroV vectors) (addV vectors)

record LeftModule
  {k v : Level}
  {K : Set k}
  {V : Set v}
  (ring : DivisionRing K)
  (vectors : AdditiveCommutativeGroup V) :
  Set (k ⊔ v) where

  field
    scale : K -> V -> V

    one-scale :
      (x : V) ->
      scale (oneK ring) x == x
    multiply-scale :
      (a b : K) ->
      (x : V) ->
      scale (multiplyK ring a b) x ==
      scale a (scale b x)
    add-scalars :
      (a b : K) ->
      (x : V) ->
      scale (addK ring a b) x ==
      addV vectors (scale a x) (scale b x)
    scale-add-vectors :
      (a : K) ->
      (x y : V) ->
      scale a (addV vectors x y) ==
      addV vectors (scale a x) (scale a y)

open LeftModule

record AffineSpace
  {v p : Level}
  {V : Set v}
  (vectors : AdditiveCommutativeGroup V)
  (P : Set p) :
  Set (v ⊔ p) where

  field
    vadd : V -> P -> P
    vsub : P -> P -> V

    zero-vadd :
      (point : P) ->
      vadd (zeroV vectors) point == point
    add-vadd :
      (u v : V) ->
      (point : P) ->
      vadd (addV vectors u v) point ==
      vadd u (vadd v point)
    vsub-vadd :
      (p q : P) ->
      vadd (vsub p q) q == p
    vadd-vsub :
      (u : V) ->
      (point : P) ->
      vsub (vadd u point) point == u

open AffineSpace

weightedDisplacement :
  {k v p : Level} ->
  {K : Set k} ->
  {V : Set v} ->
  {P : Set p} ->
  (ring : DivisionRing K) ->
  (vectors : AdditiveCommutativeGroup V) ->
  (module-structure : LeftModule ring vectors) ->
  (affine : AffineSpace vectors P) ->
  {n : Nat} ->
  (points : Fin (suc n) -> P) ->
  (coefficients : Fin (suc n) -> K) ->
  V
weightedDisplacement ring vectors module-structure affine points coefficients =
  sumV vectors
    (\ i ->
      scale module-structure
        (coefficients i)
        (vsub affine (points i) (points fzero)))

AffineIndependent :
  {k v p : Level} ->
  {K : Set k} ->
  {V : Set v} ->
  {P : Set p} ->
  (ring : DivisionRing K) ->
  (vectors : AdditiveCommutativeGroup V) ->
  (module-structure : LeftModule ring vectors) ->
  (affine : AffineSpace vectors P) ->
  {n : Nat} ->
  (Fin (suc n) -> P) ->
  Set (k ⊔ v)
AffineIndependent ring vectors module-structure affine points =
  (coefficients : Fin _ -> _) ->
  sumK ring coefficients == zeroK ring ->
  weightedDisplacement
    ring vectors module-structure affine points coefficients
    ==
    zeroV vectors ->
  (i : Fin _) ->
  coefficients i == zeroK ring

record Simplex
  {k v p : Level}
  {K : Set k}
  {V : Set v}
  {P : Set p}
  (ring : DivisionRing K)
  (vectors : AdditiveCommutativeGroup V)
  (module-structure : LeftModule ring vectors)
  (affine : AffineSpace vectors P)
  (n : Nat) :
  Set (k ⊔ v ⊔ p) where

  field
    points :
      Fin (suc n) ->
      P
    independent :
      AffineIndependent
        ring vectors module-structure affine points

open Simplex

centroid :
  {k v p : Level} ->
  {K : Set k} ->
  {V : Set v} ->
  {P : Set p} ->
  (ring : DivisionRing K) ->
  (vectors : AdditiveCommutativeGroup V) ->
  (module-structure : LeftModule ring vectors) ->
  (affine : AffineSpace vectors P) ->
  {n : Nat} ->
  (Fin (suc n) -> P) ->
  P
centroid ring vectors module-structure affine {n} points =
  vadd affine
    (scale module-structure
      (inverseK ring (natCast ring (suc n)))
      (sumV vectors
        (\ i -> vsub affine (points i) (points fzero))))
    (points fzero)

faceOppositeCentroid :
  {k v p : Level} ->
  {K : Set k} ->
  {V : Set v} ->
  {P : Set p} ->
  (ring : DivisionRing K) ->
  (vectors : AdditiveCommutativeGroup V) ->
  (module-structure : LeftModule ring vectors) ->
  (affine : AffineSpace vectors P) ->
  {n : Nat} ->
  n != zero ->
  (points : Fin (suc n) -> P) ->
  Fin (suc n) ->
  P
faceOppositeCentroid
  ring vectors module-structure affine {n} nonzero points i =
  vadd affine
    (scale module-structure
      (inverseK ring (natCast ring n))
      (sumV vectors
        (\ j -> vsub affine (points j) (points i))))
    (points i)

commandinos-theorem :
  (k v p : Level) ->
  Set (lsuc (k ⊔ v ⊔ p))
commandinos-theorem k v p =
  (K : Set k) ->
  (ring : DivisionRing K) ->
  CharZero ring ->
  (V : Set v) ->
  (vectors : AdditiveCommutativeGroup V) ->
  (module-structure : LeftModule ring vectors) ->
  (P : Set p) ->
  (affine : AffineSpace vectors P) ->
  (n : Nat) ->
  (nonzero : n != zero) ->
  (simplex : Simplex ring vectors module-structure affine n) ->
  (i : Fin (suc n)) ->
  vsub affine
    (points simplex i)
    (centroid
      ring vectors module-structure affine
      (points simplex))
  ==
  scale module-structure
    (natCast ring n)
    (vsub affine
      (centroid
        ring vectors module-structure affine
        (points simplex))
      (faceOppositeCentroid
        ring vectors module-structure affine
        nonzero
        (points simplex)
        i))
