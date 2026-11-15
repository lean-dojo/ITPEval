-- Statement-only formalization of thousand-theorems corpus artifact Q172298,
-- "Lasker–Noether theorem": a finite primary decomposition of a submodule can
-- be replaced by one whose colon-ideal radicals are pairwise distinct. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module Q172298_lasker_noether_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _and_
infixr 2 _or_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} A =
  A -> Bottom {a}

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record CommutativeSemiring
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
    multiply-commutative :
      (x y : R) ->
      multiplyR x y == multiplyR y x
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
    multiply-zero-left :
      (x : R) ->
      multiplyR zeroR x == zeroR
    multiply-zero-right :
      (x : R) ->
      multiplyR x zeroR == zeroR

record AdditiveCommutativeMonoid
  {m : Level}
  (M : Set m) :
  Set m where

  field
    zeroM : M
    addM  : M -> M -> M

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
  (semiring : CommutativeSemiring R)
  (additive : AdditiveCommutativeMonoid M) :
  Set (r ⊔ m) where

  field
    scale : R -> M -> M

    one-scale :
      (x : M) ->
      scale (CommutativeSemiring.oneR semiring) x == x
    multiply-scale :
      (a b : R) (x : M) ->
      scale (CommutativeSemiring.multiplyR semiring a b) x ==
      scale a (scale b x)
    add-scale :
      (a b : R) (x : M) ->
      scale (CommutativeSemiring.addR semiring a b) x ==
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
      scale (CommutativeSemiring.zeroR semiring) x ==
      AdditiveCommutativeMonoid.zeroM additive
    scale-zero :
      (a : R) ->
      scale a (AdditiveCommutativeMonoid.zeroM additive) ==
      AdditiveCommutativeMonoid.zeroM additive

record Submodule
  {r m : Level}
  {R : Set r}
  {M : Set m}
  (semiring : CommutativeSemiring R)
  (additive : AdditiveCommutativeMonoid M)
  (module-structure : Module semiring additive) :
  Set (r ⊔ lsuc m) where

  field
    member : M -> Set m
    membership-propositional :
      (x : M) ->
      (u v : member x) ->
      u == v
    contains-zero :
      member (AdditiveCommutativeMonoid.zeroM additive)
    closed-under-addition :
      (x y : M) ->
      member x ->
      member y ->
      member (AdditiveCommutativeMonoid.addM additive x y)
    closed-under-scaling :
      (a : R) (x : M) ->
      member x ->
      member (Module.scale module-structure a x)

SubmoduleEqual :
  {r m : Level}
  {R : Set r}
  {M : Set m}
  {semiring : CommutativeSemiring R}
  {additive : AdditiveCommutativeMonoid M}
  {module-structure : Module semiring additive} ->
  Submodule semiring additive module-structure ->
  Submodule semiring additive module-structure ->
  Set m
SubmoduleEqual {M = M} left-submodule right-submodule =
  (x : M) ->
  Iff
    (Submodule.member left-submodule x)
    (Submodule.member right-submodule x)

record FiniteSet
  {a e : Level}
  (A : Set a)
  (Equivalent : A -> A -> Set e) :
  Set (a ⊔ lsuc e) where

  field
    size : Nat
    member : A -> Set e
    membership-propositional :
      (x : A) ->
      (u v : member x) ->
      u == v
    membership-extensional :
      (x y : A) ->
      Equivalent x y ->
      Iff (member x) (member y)
    enumerate : Fin size -> A
    enumerate-member :
      (i : Fin size) ->
      member (enumerate i)
    exhaustive :
      (x : A) ->
      member x ->
      Exists (Fin size)
        (\ i -> Equivalent x (enumerate i))
    no-duplicates :
      (i j : Fin size) ->
      Equivalent (enumerate i) (enumerate j) ->
      i == j

power :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  R ->
  Nat ->
  R
power semiring x zero =
  CommutativeSemiring.oneR semiring
power semiring x (suc n) =
  CommutativeSemiring.multiplyR semiring x
    (power semiring x n)

RadicalAnnihilator :
  {r m : Level}
  {R : Set r}
  {M : Set m}
  (semiring : CommutativeSemiring R)
  (additive : AdditiveCommutativeMonoid M)
  (module-structure : Module semiring additive) ->
  Submodule semiring additive module-structure ->
  R ->
  Set m
RadicalAnnihilator {M = M}
    semiring additive module-structure submodule scalar =
  Exists Nat
    (\ exponent ->
      (x : M) ->
      Submodule.member submodule
        (Module.scale module-structure
          (power semiring scalar exponent)
          x))

record IsPrimary
  {r m : Level}
  {R : Set r}
  {M : Set m}
  (semiring : CommutativeSemiring R)
  (additive : AdditiveCommutativeMonoid M)
  (module-structure : Module semiring additive)
  (submodule : Submodule semiring additive module-structure) :
  Set (r ⊔ m) where

  field
    proper :
      Not ((x : M) -> Submodule.member submodule x)
    primary-condition :
      (scalar : R) ->
      (x : M) ->
      Submodule.member submodule
        (Module.scale module-structure scalar x) ->
      Submodule.member submodule x or
      RadicalAnnihilator
        semiring additive module-structure submodule scalar

FiniteSubmodules :
  {r m : Level}
  {R : Set r}
  {M : Set m}
  (semiring : CommutativeSemiring R)
  (additive : AdditiveCommutativeMonoid M)
  (module-structure : Module semiring additive) ->
  Set (r ⊔ lsuc m)
FiniteSubmodules semiring additive module-structure =
  FiniteSet
    (Submodule semiring additive module-structure)
    SubmoduleEqual

Intersection :
  {r m : Level}
  {R : Set r}
  {M : Set m}
  {semiring : CommutativeSemiring R}
  {additive : AdditiveCommutativeMonoid M}
  {module-structure : Module semiring additive} ->
  FiniteSubmodules semiring additive module-structure ->
  M ->
  Set (r ⊔ lsuc m)
Intersection {semiring = semiring}
    {additive = additive}
    {module-structure = module-structure}
    family x =
  (submodule : Submodule semiring additive module-structure) ->
  FiniteSet.member family submodule ->
  Submodule.member submodule x

IntersectionEqual :
  {r m : Level}
  {R : Set r}
  {M : Set m}
  {semiring : CommutativeSemiring R}
  {additive : AdditiveCommutativeMonoid M}
  {module-structure : Module semiring additive} ->
  FiniteSubmodules semiring additive module-structure ->
  Submodule semiring additive module-structure ->
  Set (r ⊔ lsuc m)
IntersectionEqual {M = M} family submodule =
  (x : M) ->
  Iff
    (Intersection family x)
    (Submodule.member submodule x)

AllPrimary :
  {r m : Level}
  {R : Set r}
  {M : Set m}
  (semiring : CommutativeSemiring R)
  (additive : AdditiveCommutativeMonoid M)
  (module-structure : Module semiring additive) ->
  FiniteSubmodules semiring additive module-structure ->
  Set (r ⊔ lsuc m)
AllPrimary semiring additive module-structure family =
  (submodule : Submodule semiring additive module-structure) ->
  FiniteSet.member family submodule ->
  IsPrimary semiring additive module-structure submodule

RadicalEqual :
  {r m : Level}
  {R : Set r}
  {M : Set m}
  (semiring : CommutativeSemiring R)
  (additive : AdditiveCommutativeMonoid M)
  (module-structure : Module semiring additive) ->
  Submodule semiring additive module-structure ->
  Submodule semiring additive module-structure ->
  Set (r ⊔ m)
RadicalEqual {R = R}
    semiring additive module-structure left-submodule right-submodule =
  (scalar : R) ->
  Iff
    (RadicalAnnihilator
      semiring additive module-structure left-submodule scalar)
    (RadicalAnnihilator
      semiring additive module-structure right-submodule scalar)

PairwiseDistinctRadicals :
  {r m : Level}
  {R : Set r}
  {M : Set m}
  (semiring : CommutativeSemiring R)
  (additive : AdditiveCommutativeMonoid M)
  (module-structure : Module semiring additive) ->
  FiniteSubmodules semiring additive module-structure ->
  Set (r ⊔ lsuc m)
PairwiseDistinctRadicals
    semiring additive module-structure family =
  (left-submodule right-submodule :
    Submodule semiring additive module-structure) ->
  FiniteSet.member family left-submodule ->
  FiniteSet.member family right-submodule ->
  Not (SubmoduleEqual left-submodule right-submodule) ->
  Not
    (RadicalEqual
      semiring additive module-structure
      left-submodule right-submodule)

-- Lean: Ideal.isPrimary_decomposition_pairwise_ne_radical
lasker-noether-theorem : Setω
lasker-noether-theorem =
  {r m : Level} ->
  (R : Set r) ->
  (M : Set m) ->
  (semiring : CommutativeSemiring R) ->
  (additive : AdditiveCommutativeMonoid M) ->
  (module-structure : Module semiring additive) ->
  (N : Submodule semiring additive module-structure) ->
  (s : FiniteSubmodules semiring additive module-structure) ->
  IntersectionEqual s N ->
  AllPrimary semiring additive module-structure s ->
  Exists
    (FiniteSubmodules semiring additive module-structure)
    (\ t ->
      IntersectionEqual t N and
      (AllPrimary semiring additive module-structure t and
      PairwiseDistinctRadicals
        semiring additive module-structure t))
