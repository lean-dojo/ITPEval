-- Statement-only formalization of thousand-theorems corpus artifact Q303402,
-- "Rank–nullity theorem": for a linear map over a ring satisfying rank-nullity,
-- the cardinal rank of its range plus that of its kernel equals the rank of its
-- domain. This file contains no proof.

{-# OPTIONS --safe #-}

module Q303402_rank_nullity_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

infixr 5 _sum_
infixr 5 _vcons_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} A =
  A -> Bottom {a}

symmetry :
  {a : Level} ->
  {A : Set a} ->
  {x y : A} ->
  x == y ->
  y == x
symmetry refl =
  refl

transitivity :
  {a : Level} ->
  {A : Set a} ->
  {x y z : A} ->
  x == y ->
  y == z ->
  x == z
transitivity refl refl =
  refl

congruence :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (f : A -> B) ->
  {x y : A} ->
  x == y ->
  f x == f y
congruence f refl =
  refl

congruence-two :
  {a b c : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  {C : Set c} ->
  (f : A -> B -> C) ->
  {x x' : A} ->
  {y y' : B} ->
  x == x' ->
  y == y' ->
  f x y == f x' y'
congruence-two f refl refl =
  refl

data _sum_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A sum B
  right : B -> A sum B

record Injection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    apply :
      A -> B
    injective :
      (x y : A) ->
      apply x == apply y ->
      x == y

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

data Fin : Nat -> Set where
  first : {n : Nat} -> Fin (suc n)
  next  : {n : Nat} -> Fin n -> Fin (suc n)

data Vec
  {a : Level}
  (A : Set a) :
  Nat ->
  Set a where

  empty :
    Vec A zero
  _vcons_ :
    {n : Nat} ->
    A ->
    Vec A n ->
    Vec A (suc n)

lookup :
  {a : Level} ->
  {A : Set a} ->
  {n : Nat} ->
  Vec A n ->
  Fin n ->
  A
lookup (x vcons xs) first =
  x
lookup (x vcons xs) (next i) =
  lookup xs i

data NotMember
  {a : Level}
  {A : Set a}
  (x : A) :
  {n : Nat} ->
  Vec A n ->
  Set a where

  not-in-empty :
    NotMember x empty
  not-in-cons :
    {n : Nat} ->
    {y : A} ->
    {ys : Vec A n} ->
    Not (x == y) ->
    NotMember x ys ->
    NotMember x (y vcons ys)

data Distinct
  {a : Level}
  {A : Set a} :
  {n : Nat} ->
  Vec A n ->
  Set a where

  distinct-empty :
    Distinct empty
  distinct-cons :
    {n : Nat} ->
    {x : A} ->
    {xs : Vec A n} ->
    NotMember x xs ->
    Distinct xs ->
    Distinct (x vcons xs)

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
    scale :
      R -> M -> M
    one-scale :
      (x : M) ->
      scale (Ring.oneR ring) x == x
    multiply-scale :
      (a b : R) (x : M) ->
      scale (Ring.multiplyR ring a b) x ==
      scale a (scale b x)
    add-scale :
      (a b : R) (x : M) ->
      scale (Ring.addR ring a b) x ==
      AdditiveCommutativeGroup.addM additive
        (scale a x)
        (scale b x)
    scale-add :
      (a : R) (x y : M) ->
      scale a (AdditiveCommutativeGroup.addM additive x y) ==
      AdditiveCommutativeGroup.addM additive
        (scale a x)
        (scale a y)
    zero-scale :
      (x : M) ->
      scale (Ring.zeroR ring) x ==
      AdditiveCommutativeGroup.zeroM additive
    scale-zero :
      (a : R) ->
      scale a (AdditiveCommutativeGroup.zeroM additive) ==
      AdditiveCommutativeGroup.zeroM additive

record LinearMap
  {r m : Level}
  {R : Set r}
  {M N : Set m}
  {ring : Ring R}
  {source-additive : AdditiveCommutativeGroup M}
  {target-additive : AdditiveCommutativeGroup N}
  (source-module : Module ring source-additive)
  (target-module : Module ring target-additive) :
  Set (r ⊔ m) where

  field
    apply :
      M -> N
    map-zero :
      apply (AdditiveCommutativeGroup.zeroM source-additive) ==
      AdditiveCommutativeGroup.zeroM target-additive
    map-add :
      (x y : M) ->
      apply (AdditiveCommutativeGroup.addM source-additive x y) ==
      AdditiveCommutativeGroup.addM target-additive
        (apply x)
        (apply y)
    map-negate :
      (x : M) ->
      apply (AdditiveCommutativeGroup.negateM source-additive x) ==
      AdditiveCommutativeGroup.negateM target-additive (apply x)
    map-scale :
      (a : R) (x : M) ->
      apply (Module.scale source-module a x) ==
      Module.scale target-module a (apply x)

record Submodule
  {r m : Level}
  {R : Set r}
  {M : Set m}
  {ring : Ring R}
  {additive : AdditiveCommutativeGroup M}
  (module-structure : Module ring additive) :
  Set (r ⊔ lsuc m) where

  field
    member :
      M -> Set m
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
      (a : R) (x : M) ->
      member x ->
      member (Module.scale module-structure a x)

Kernel :
  {r m : Level} ->
  {R : Set r} ->
  {M N : Set m} ->
  {ring : Ring R} ->
  {source-additive : AdditiveCommutativeGroup M} ->
  {target-additive : AdditiveCommutativeGroup N} ->
  {source-module : Module ring source-additive} ->
  {target-module : Module ring target-additive} ->
  LinearMap source-module target-module ->
  M ->
  Set m
Kernel {target-additive = target-additive} linear-map x =
  LinearMap.apply linear-map x ==
  AdditiveCommutativeGroup.zeroM target-additive

Range :
  {r m : Level} ->
  {R : Set r} ->
  {M N : Set m} ->
  {ring : Ring R} ->
  {source-additive : AdditiveCommutativeGroup M} ->
  {target-additive : AdditiveCommutativeGroup N} ->
  {source-module : Module ring source-additive} ->
  {target-module : Module ring target-additive} ->
  LinearMap source-module target-module ->
  N ->
  Set m
Range {M = M} linear-map y =
  Σ M (\ x -> LinearMap.apply linear-map x == y)

kernelSubmodule :
  {r m : Level} ->
  {R : Set r} ->
  {M N : Set m} ->
  {ring : Ring R} ->
  {source-additive : AdditiveCommutativeGroup M} ->
  {target-additive : AdditiveCommutativeGroup N} ->
  {source-module : Module ring source-additive} ->
  {target-module : Module ring target-additive} ->
  (linear-map : LinearMap source-module target-module) ->
  Submodule source-module
kernelSubmodule
    {source-additive = source-additive}
    {target-additive = target-additive}
    {source-module = source-module}
    {target-module = target-module}
    linear-map =
  record
    { member = Kernel linear-map
    ; contains-zero = LinearMap.map-zero linear-map
    ; closed-under-addition =
        \ x y hx hy ->
          transitivity
            (LinearMap.map-add linear-map x y)
            (transitivity
              (congruence-two
                (AdditiveCommutativeGroup.addM target-additive)
                hx hy)
              (AdditiveCommutativeGroup.add-zero-left
                target-additive
                (AdditiveCommutativeGroup.zeroM target-additive)))
    ; closed-under-negation =
        \ x hx ->
          transitivity
            (LinearMap.map-negate linear-map x)
            (transitivity
              (congruence
                (AdditiveCommutativeGroup.negateM target-additive)
                hx)
              (transitivity
                (symmetry
                  (AdditiveCommutativeGroup.add-zero-right
                    target-additive
                    (AdditiveCommutativeGroup.negateM target-additive
                      (AdditiveCommutativeGroup.zeroM target-additive))))
                (AdditiveCommutativeGroup.add-inverse-left
                  target-additive
                  (AdditiveCommutativeGroup.zeroM target-additive))))
    ; closed-under-scaling =
        \ a x hx ->
          transitivity
            (LinearMap.map-scale linear-map a x)
            (transitivity
              (congruence
                (Module.scale target-module a)
                hx)
              (Module.scale-zero target-module a))
    }

rangeSubmodule :
  {r m : Level} ->
  {R : Set r} ->
  {M N : Set m} ->
  {ring : Ring R} ->
  {source-additive : AdditiveCommutativeGroup M} ->
  {target-additive : AdditiveCommutativeGroup N} ->
  {source-module : Module ring source-additive} ->
  {target-module : Module ring target-additive} ->
  (linear-map : LinearMap source-module target-module) ->
  Submodule target-module
rangeSubmodule
    {source-additive = source-additive}
    {target-additive = target-additive}
    {source-module = source-module}
    {target-module = target-module}
    linear-map =
  record
    { member = Range linear-map
    ; contains-zero =
        AdditiveCommutativeGroup.zeroM source-additive ,
        LinearMap.map-zero linear-map
    ; closed-under-addition =
        \ y z hy hz ->
          AdditiveCommutativeGroup.addM source-additive
            (fst hy) (fst hz) ,
          transitivity
            (LinearMap.map-add linear-map (fst hy) (fst hz))
            (congruence-two
              (AdditiveCommutativeGroup.addM target-additive)
              (snd hy) (snd hz))
    ; closed-under-negation =
        \ y hy ->
          AdditiveCommutativeGroup.negateM source-additive (fst hy) ,
          transitivity
            (LinearMap.map-negate linear-map (fst hy))
            (congruence
              (AdditiveCommutativeGroup.negateM target-additive)
              (snd hy))
    ; closed-under-scaling =
        \ a y hy ->
          Module.scale source-module a (fst hy) ,
          transitivity
            (LinearMap.map-scale linear-map a (fst hy))
            (congruence
              (Module.scale target-module a)
              (snd hy))
    }

linearCombination :
  {r m i : Level} ->
  {R : Set r} ->
  {M : Set m} ->
  {I : Set i} ->
  {ring : Ring R} ->
  (additive : AdditiveCommutativeGroup M) ->
  (module-structure : Module ring additive) ->
  (vectors : I -> M) ->
  {n : Nat} ->
  Vec I n ->
  Vec R n ->
  M
linearCombination additive module-structure vectors empty empty =
  AdditiveCommutativeGroup.zeroM additive
linearCombination additive module-structure vectors
    (index vcons indices) (coefficient vcons coefficients) =
  AdditiveCommutativeGroup.addM additive
    (Module.scale module-structure coefficient (vectors index))
    (linearCombination additive module-structure vectors
      indices coefficients)

LinearIndependent :
  {r m i : Level} ->
  {R : Set r} ->
  {M : Set m} ->
  {I : Set i} ->
  {ring : Ring R} ->
  (additive : AdditiveCommutativeGroup M) ->
  (module-structure : Module ring additive) ->
  (vectors : I -> M) ->
  Set (r ⊔ m ⊔ i)
LinearIndependent {R = R} {I = I} {ring = ring}
    additive module-structure vectors =
  (n : Nat) ->
  (indices : Vec I n) ->
  (coefficients : Vec R n) ->
  Distinct indices ->
  linearCombination additive module-structure vectors
    indices coefficients ==
    AdditiveCommutativeGroup.zeroM additive ->
  (position : Fin n) ->
  lookup coefficients position == Ring.zeroR ring

QuotientLinearIndependent :
  {r m i : Level} ->
  {R : Set r} ->
  {M : Set m} ->
  {I : Set i} ->
  {ring : Ring R} ->
  {additive : AdditiveCommutativeGroup M} ->
  (module-structure : Module ring additive) ->
  Submodule module-structure ->
  (I -> M) ->
  Set (r ⊔ m ⊔ i)
QuotientLinearIndependent
    {R = R} {I = I} {ring = ring} {additive = additive}
    module-structure submodule vectors =
  (n : Nat) ->
  (indices : Vec I n) ->
  (coefficients : Vec R n) ->
  Distinct indices ->
  Submodule.member submodule
    (linearCombination additive module-structure vectors
      indices coefficients) ->
  (position : Fin n) ->
  lookup coefficients position == Ring.zeroR ring

record RankData
  {r m : Level}
  {R : Set r}
  {M : Set m}
  {ring : Ring R}
  (additive : AdditiveCommutativeGroup M)
  (module-structure : Module ring additive) :
  Set (r ⊔ lsuc m) where

  field
    Index :
      Set m
    vectors :
      Index -> M
    linearly-independent :
      LinearIndependent additive module-structure vectors
    maximal :
      {J : Set m} ->
      (other-vectors : J -> M) ->
      LinearIndependent additive module-structure other-vectors ->
      Injection J Index

record SubmoduleRankData
  {r m : Level}
  {R : Set r}
  {M : Set m}
  {ring : Ring R}
  {additive : AdditiveCommutativeGroup M}
  (module-structure : Module ring additive)
  (submodule : Submodule module-structure) :
  Set (r ⊔ lsuc m) where

  field
    Index :
      Set m
    vectors :
      Index -> M
    vectors-belong :
      (i : Index) ->
      Submodule.member submodule (vectors i)
    linearly-independent :
      LinearIndependent additive module-structure vectors
    maximal :
      {J : Set m} ->
      (other-vectors : J -> M) ->
      ((j : J) ->
        Submodule.member submodule (other-vectors j)) ->
      LinearIndependent additive module-structure other-vectors ->
      Injection J Index

record QuotientRankData
  {r m : Level}
  {R : Set r}
  {M : Set m}
  {ring : Ring R}
  {additive : AdditiveCommutativeGroup M}
  (module-structure : Module ring additive)
  (submodule : Submodule module-structure) :
  Set (r ⊔ lsuc m) where

  field
    Index :
      Set m
    representatives :
      Index -> M
    quotient-linearly-independent :
      QuotientLinearIndependent
        module-structure submodule representatives
    maximal :
      {J : Set m} ->
      (other-representatives : J -> M) ->
      QuotientLinearIndependent
        module-structure submodule other-representatives ->
      Injection J Index

record HasRankNullity
  {r m : Level}
  {R : Set r}
  (ring : Ring R) :
  Set (r ⊔ lsuc m) where

  field
    module-rank :
      (M : Set m) ->
      (additive : AdditiveCommutativeGroup M) ->
      (module-structure : Module ring additive) ->
      RankData additive module-structure
    submodule-rank :
      (M : Set m) ->
      (additive : AdditiveCommutativeGroup M) ->
      (module-structure : Module ring additive) ->
      (submodule : Submodule module-structure) ->
      SubmoduleRankData module-structure submodule
    quotient-rank :
      (M : Set m) ->
      (additive : AdditiveCommutativeGroup M) ->
      (module-structure : Module ring additive) ->
      (submodule : Submodule module-structure) ->
      QuotientRankData module-structure submodule
    rank-quotient-add-rank :
      (M : Set m) ->
      (additive : AdditiveCommutativeGroup M) ->
      (module-structure : Module ring additive) ->
      (submodule : Submodule module-structure) ->
      Bijection
        (QuotientRankData.Index
          (quotient-rank M additive module-structure submodule)
          sum
        SubmoduleRankData.Index
          (submodule-rank M additive module-structure submodule))
        (RankData.Index
          (module-rank M additive module-structure))

ModuleRankIndex :
  {r m : Level} ->
  {R : Set r} ->
  {ring : Ring R} ->
  (rank-nullity : HasRankNullity {m = m} ring) ->
  (M : Set m) ->
  (additive : AdditiveCommutativeGroup M) ->
  (module-structure : Module ring additive) ->
  Set m
ModuleRankIndex rank-nullity M additive module-structure =
  RankData.Index
    (HasRankNullity.module-rank rank-nullity
      M additive module-structure)

SubmoduleRankIndex :
  {r m : Level} ->
  {R : Set r} ->
  {ring : Ring R} ->
  (rank-nullity : HasRankNullity {m = m} ring) ->
  (M : Set m) ->
  (additive : AdditiveCommutativeGroup M) ->
  (module-structure : Module ring additive) ->
  Submodule module-structure ->
  Set m
SubmoduleRankIndex rank-nullity M additive module-structure submodule =
  SubmoduleRankData.Index
    (HasRankNullity.submodule-rank rank-nullity
      M additive module-structure submodule)

-- Lean: LinearMap.rank_range_add_rank_ker
rank-nullity-theorem : Setω
rank-nullity-theorem =
  {r m : Level} ->
  (R : Set r) ->
  (M M1 : Set m) ->
  (ring : Ring R) ->
  (source-additive : AdditiveCommutativeGroup M) ->
  (target-additive : AdditiveCommutativeGroup M1) ->
  (source-module : Module ring source-additive) ->
  (target-module : Module ring target-additive) ->
  (has-rank-nullity : HasRankNullity {m = m} ring) ->
  (linear-map : LinearMap source-module target-module) ->
  Bijection
    (SubmoduleRankIndex has-rank-nullity
      M1 target-additive target-module
      (rangeSubmodule linear-map)
      sum
    SubmoduleRankIndex has-rank-nullity
      M source-additive source-module
      (kernelSubmodule linear-map))
    (ModuleRankIndex has-rank-nullity
      M source-additive source-module)
