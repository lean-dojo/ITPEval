-- Statement-only formalization of thousand-theorems corpus artifact Q17098298,
-- "Jacobson density theorem": on a semisimple module, every additive self-map
-- commuting with all module endomorphisms agrees on each finite subset with
-- scalar multiplication by one ring element. This file contains no proof.

{-# OPTIONS --safe #-}

module Q17098298_jacobson_density_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Ring
  {r : Level}
  (R : Set r) :
  Set r where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR : R -> R

    add-associative :
      (x y z : R) ->
      addR (addR x y) z ==
      addR x (addR y z)
    add-commutative :
      (x y : R) ->
      addR x y == addR y x
    add-zero-left :
      (x : R) ->
      addR zeroR x == x
    add-zero-right :
      (x : R) ->
      addR x zeroR == x
    add-inverse-left :
      (x : R) ->
      addR (negateR x) x == zeroR
    add-inverse-right :
      (x : R) ->
      addR x (negateR x) == zeroR

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

    distribute-left :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : R) ->
      multiplyR (addR x y) z ==
      addR (multiplyR x z) (multiplyR y z)

record AdditiveCommutativeGroup
  {m : Level}
  (M : Set m) :
  Set m where

  field
    zeroM : M
    addM : M -> M -> M
    negateM : M -> M

    add-associative :
      (x y z : M) ->
      addM (addM x y) z ==
      addM x (addM y z)
    add-commutative :
      (x y : M) ->
      addM x y == addM y x
    add-zero-left :
      (x : M) ->
      addM zeroM x == x
    add-zero-right :
      (x : M) ->
      addM x zeroM == x
    add-inverse-left :
      (x : M) ->
      addM (negateM x) x == zeroM
    add-inverse-right :
      (x : M) ->
      addM x (negateM x) == zeroM

record Module
  {r m : Level}
  {R : Set r}
  {M : Set m}
  (ring : Ring R)
  (additive : AdditiveCommutativeGroup M) :
  Set (r ⊔ m) where

  field
    scale : R -> M -> M

    one-scale :
      (x : M) ->
      scale (Ring.oneR ring) x == x
    multiply-scale :
      (a b : R) ->
      (x : M) ->
      scale (Ring.multiplyR ring a b) x ==
      scale a (scale b x)
    add-scale :
      (a b : R) ->
      (x : M) ->
      scale (Ring.addR ring a b) x ==
      AdditiveCommutativeGroup.addM additive
        (scale a x)
        (scale b x)
    scale-add :
      (a : R) ->
      (x y : M) ->
      scale a (AdditiveCommutativeGroup.addM additive x y) ==
      AdditiveCommutativeGroup.addM additive
        (scale a x)
        (scale a y)

record LinearEndomorphism
  {r m : Level}
  {R : Set r}
  {M : Set m}
  {ring : Ring R}
  {additive : AdditiveCommutativeGroup M}
  (module-structure : Module ring additive) :
  Set (r ⊔ m) where

  field
    apply : M -> M
    map-zero :
      apply (AdditiveCommutativeGroup.zeroM additive) ==
      AdditiveCommutativeGroup.zeroM additive
    map-add :
      (x y : M) ->
      apply (AdditiveCommutativeGroup.addM additive x y) ==
      AdditiveCommutativeGroup.addM additive
        (apply x)
        (apply y)
    map-scale :
      (a : R) ->
      (x : M) ->
      apply (Module.scale module-structure a x) ==
      Module.scale module-structure a (apply x)

record EndomorphismLinearMap
  {r m : Level}
  {R : Set r}
  {M : Set m}
  {ring : Ring R}
  {additive : AdditiveCommutativeGroup M}
  (module-structure : Module ring additive) :
  Set (r ⊔ m) where

  field
    apply : M -> M
    map-zero :
      apply (AdditiveCommutativeGroup.zeroM additive) ==
      AdditiveCommutativeGroup.zeroM additive
    map-add :
      (x y : M) ->
      apply (AdditiveCommutativeGroup.addM additive x y) ==
      AdditiveCommutativeGroup.addM additive
        (apply x)
        (apply y)
    commutes-with-endomorphisms :
      (g : LinearEndomorphism module-structure) ->
      (x : M) ->
      apply (LinearEndomorphism.apply g x) ==
      LinearEndomorphism.apply g (apply x)

record Submodule
  {r m : Level}
  {R : Set r}
  {M : Set m}
  {ring : Ring R}
  {additive : AdditiveCommutativeGroup M}
  (module-structure : Module ring additive) :
  Set (r ⊔ lsuc m) where

  field
    member : M -> Set m
    membership-propositional :
      (x : M) ->
      (u v : member x) ->
      u == v
    contains-zero :
      member (AdditiveCommutativeGroup.zeroM additive)
    closed-under-addition :
      (x y : M) ->
      member x ->
      member y ->
      member (AdditiveCommutativeGroup.addM additive x y)
    closed-under-negation :
      (x : M) ->
      member x ->
      member (AdditiveCommutativeGroup.negateM additive x)
    closed-under-scaling :
      (a : R) ->
      (x : M) ->
      member x ->
      member (Module.scale module-structure a x)

record DirectComplement
  {r m : Level}
  {R : Set r}
  {M : Set m}
  {ring : Ring R}
  {additive : AdditiveCommutativeGroup M}
  {module-structure : Module ring additive}
  (left right : Submodule module-structure) :
  Set (r ⊔ m) where

  field
    intersection-zero :
      (x : M) ->
      Submodule.member left x ->
      Submodule.member right x ->
      x == AdditiveCommutativeGroup.zeroM additive
    spans :
      (x : M) ->
      Σ M
        (\ left-part ->
          Σ (Submodule.member left left-part)
            (\ _ ->
              Σ M
                (\ right-part ->
                  Σ (Submodule.member right right-part)
                    (\ _ ->
                      x ==
                      AdditiveCommutativeGroup.addM additive
                        left-part right-part))))

IsSemisimpleModule :
  {r m : Level} ->
  {R : Set r} ->
  {M : Set m} ->
  {ring : Ring R} ->
  {additive : AdditiveCommutativeGroup M} ->
  Module ring additive ->
  Set (r ⊔ lsuc m)
IsSemisimpleModule module-structure =
  (left : Submodule module-structure) ->
  Σ (Submodule module-structure)
    (\ right ->
      DirectComplement left right)

record FiniteSubset
  {m : Level}
  (M : Set m) :
  Set (lsuc m) where

  field
    size : Nat
    member : M -> Set m
    membership-propositional :
      (x : M) ->
      (u v : member x) ->
      u == v
    enumerate : Fin size -> M
    enumerate-member :
      (i : Fin size) ->
      member (enumerate i)
    exhaustive :
      (x : M) ->
      member x ->
      Σ (Fin size)
        (\ i ->
          enumerate i == x)
    no-duplicates :
      (i j : Fin size) ->
      enumerate i == enumerate j ->
      i == j

jacobson-density-theorem : Setω
jacobson-density-theorem =
  {r m : Level} ->
  (R : Set r) ->
  (M : Set m) ->
  (ring : Ring R) ->
  (additive : AdditiveCommutativeGroup M) ->
  (module-structure : Module ring additive) ->
  IsSemisimpleModule module-structure ->
  (f : EndomorphismLinearMap module-structure) ->
  (finite-subset : FiniteSubset M) ->
  Σ R
    (\ scalar ->
      (x : M) ->
      FiniteSubset.member finite-subset x ->
      EndomorphismLinearMap.apply f x ==
      Module.scale module-structure scalar x)
