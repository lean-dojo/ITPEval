-- Statement-only formalization of thousand-theorems corpus artifact Q656198,
-- "Maschke's theorem": for a finite group over a field in which the group
-- cardinality is nonzero, every invariant subspace of a linear representation
-- has an invariant direct complement. This file contains no proof.

{-# OPTIONS --safe #-}

module Q656198_maschke_s_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
  renaming (zero to zeroN; suc to sucN)
open import Agda.Builtin.Sigma using (Σ)

data Empty : Set where

Not :
  {a : Level} →
  Set a →
  Set a
Not A =
  A → Empty

infix 4 _≠_

_≠_ :
  {a : Level} →
  {A : Set a} →
  A →
  A →
  Set a
x ≠ y =
  Not (x ≡ y)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (sucN n)
  fsuc  : {n : Nat} → Fin n → Fin (sucN n)

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

record FiniteCard
  {g : Level}
  (G : Set g) :
  Set g where

  field
    cardinality : Nat
    equivalence : Bijection G (Fin cardinality)

record Group
  {g : Level}
  (G : Set g) :
  Set g where

  field
    identity : G
    inverse : G → G
    multiply : G → G → G

    multiply-associative :
      (x y z : G) →
      multiply (multiply x y) z ≡
      multiply x (multiply y z)
    identity-left :
      (x : G) →
      multiply identity x ≡ x
    identity-right :
      (x : G) →
      multiply x identity ≡ x
    inverse-left :
      (x : G) →
      multiply (inverse x) x ≡ identity
    inverse-right :
      (x : G) →
      multiply x (inverse x) ≡ identity

record Field
  {k : Level}
  (K : Set k) :
  Set k where

  field
    zero one : K
    add multiply : K → K → K
    negate inverse : K → K

    add-associative :
      (x y z : K) →
      add (add x y) z ≡ add x (add y z)
    add-commutative :
      (x y : K) →
      add x y ≡ add y x
    add-zero-left :
      (x : K) →
      add zero x ≡ x
    add-zero-right :
      (x : K) →
      add x zero ≡ x
    add-inverse-left :
      (x : K) →
      add (negate x) x ≡ zero
    add-inverse-right :
      (x : K) →
      add x (negate x) ≡ zero

    multiply-associative :
      (x y z : K) →
      multiply (multiply x y) z ≡
      multiply x (multiply y z)
    multiply-commutative :
      (x y : K) →
      multiply x y ≡ multiply y x
    multiply-one-left :
      (x : K) →
      multiply one x ≡ x
    multiply-one-right :
      (x : K) →
      multiply x one ≡ x
    multiply-zero-left :
      (x : K) →
      multiply zero x ≡ zero
    multiply-zero-right :
      (x : K) →
      multiply x zero ≡ zero

    distribute-left :
      (x y z : K) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    distribute-right :
      (x y z : K) →
      multiply (add x y) z ≡
      add (multiply x z) (multiply y z)

    zero-not-one :
      zero ≠ one
    inverse-zero :
      inverse zero ≡ zero
    inverse-left :
      (x : K) →
      x ≠ zero →
      multiply (inverse x) x ≡ one
    inverse-right :
      (x : K) →
      x ≠ zero →
      multiply x (inverse x) ≡ one

natCast :
  {k : Level} →
  {K : Set k} →
  Field K →
  Nat →
  K
natCast scalarField zeroN =
  Field.zero scalarField
natCast scalarField (sucN n) =
  Field.add
    scalarField
    (natCast scalarField n)
    (Field.one scalarField)

record AdditiveCommutativeGroup
  {v : Level}
  (V : Set v) :
  Set v where

  field
    zero : V
    add : V → V → V
    negate : V → V

    add-associative :
      (x y z : V) →
      add (add x y) z ≡ add x (add y z)
    add-commutative :
      (x y : V) →
      add x y ≡ add y x
    add-zero-left :
      (x : V) →
      add zero x ≡ x
    add-zero-right :
      (x : V) →
      add x zero ≡ x
    add-inverse-left :
      (x : V) →
      add (negate x) x ≡ zero
    add-inverse-right :
      (x : V) →
      add x (negate x) ≡ zero

record VectorSpace
  {k v : Level}
  {K : Set k}
  {V : Set v}
  (scalarField : Field K)
  (additive : AdditiveCommutativeGroup V) :
  Set (k ⊔ v) where

  field
    scale : K → V → V

    one-scale :
      (x : V) →
      scale (Field.one scalarField) x ≡ x
    multiply-scale :
      (a b : K) →
      (x : V) →
      scale (Field.multiply scalarField a b) x ≡
      scale a (scale b x)
    add-scale :
      (a b : K) →
      (x : V) →
      scale (Field.add scalarField a b) x ≡
      AdditiveCommutativeGroup.add additive
        (scale a x)
        (scale b x)
    scale-add :
      (a : K) →
      (x y : V) →
      scale a (AdditiveCommutativeGroup.add additive x y) ≡
      AdditiveCommutativeGroup.add additive
        (scale a x)
        (scale a y)
    zero-scale :
      (x : V) →
      scale (Field.zero scalarField) x ≡
      AdditiveCommutativeGroup.zero additive
    scale-zero :
      (a : K) →
      scale a (AdditiveCommutativeGroup.zero additive) ≡
      AdditiveCommutativeGroup.zero additive

record Representation
  {k g v : Level}
  {K : Set k}
  {G : Set g}
  {V : Set v}
  (scalarField : Field K)
  (group : Group G)
  (additive : AdditiveCommutativeGroup V)
  (space : VectorSpace scalarField additive) :
  Set (k ⊔ g ⊔ v) where

  field
    act : G → V → V

    identity-act :
      (x : V) →
      act (Group.identity group) x ≡ x
    multiply-act :
      (g h : G) →
      (x : V) →
      act (Group.multiply group g h) x ≡
      act g (act h x)
    act-zero :
      (g : G) →
      act g (AdditiveCommutativeGroup.zero additive) ≡
      AdditiveCommutativeGroup.zero additive
    act-add :
      (g : G) →
      (x y : V) →
      act g (AdditiveCommutativeGroup.add additive x y) ≡
      AdditiveCommutativeGroup.add additive
        (act g x)
        (act g y)
    act-scale :
      (g : G) →
      (a : K) →
      (x : V) →
      act g (VectorSpace.scale space a x) ≡
      VectorSpace.scale space a (act g x)

record InvariantSubspace
  {k g v : Level}
  {K : Set k}
  {G : Set g}
  {V : Set v}
  {scalarField : Field K}
  {group : Group G}
  {additive : AdditiveCommutativeGroup V}
  {space : VectorSpace scalarField additive}
  (representation : Representation scalarField group additive space) :
  Set (k ⊔ g ⊔ lsuc v) where

  field
    member : V → Set v
    membership-propositional :
      (x : V) →
      (u w : member x) →
      u ≡ w
    contains-zero :
      member (AdditiveCommutativeGroup.zero additive)
    closed-under-addition :
      (x y : V) →
      member x →
      member y →
      member (AdditiveCommutativeGroup.add additive x y)
    closed-under-negation :
      (x : V) →
      member x →
      member (AdditiveCommutativeGroup.negate additive x)
    closed-under-scaling :
      (a : K) →
      (x : V) →
      member x →
      member (VectorSpace.scale space a x)
    invariant :
      (g : G) →
      (x : V) →
      member x →
      member (Representation.act representation g x)

record DirectComplement
  {k g v : Level}
  {K : Set k}
  {G : Set g}
  {V : Set v}
  {scalarField : Field K}
  {group : Group G}
  {additive : AdditiveCommutativeGroup V}
  {space : VectorSpace scalarField additive}
  {representation : Representation scalarField group additive space}
  (left right : InvariantSubspace representation) :
  Set (k ⊔ g ⊔ v) where

  field
    intersection-zero :
      (x : V) →
      InvariantSubspace.member left x →
      InvariantSubspace.member right x →
      x ≡ AdditiveCommutativeGroup.zero additive
    spans :
      (x : V) →
      Σ V
        (λ left-part →
          Σ (InvariantSubspace.member left left-part)
            (λ _ →
              Σ V
                (λ right-part →
                  Σ (InvariantSubspace.member right right-part)
                    (λ _ →
                      x ≡
                      AdditiveCommutativeGroup.add additive
                        left-part
                        right-part))))

maschke-s-theorem : Setω
maschke-s-theorem =
  ∀ {k g v : Level} →
  (K : Set k) →
  (scalarField : Field K) →
  (G : Set g) →
  (group : Group G) →
  (finite : FiniteCard G) →
  natCast scalarField (FiniteCard.cardinality finite) ≠
    Field.zero scalarField →
  (V : Set v) →
  (additive : AdditiveCommutativeGroup V) →
  (space : VectorSpace scalarField additive) →
  (representation : Representation scalarField group additive space) →
  (p : InvariantSubspace representation) →
  Σ (InvariantSubspace representation)
    (λ q → DirectComplement p q)
