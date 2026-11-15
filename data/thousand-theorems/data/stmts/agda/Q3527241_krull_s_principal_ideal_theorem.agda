-- Statement-only formalization of thousand-theorems corpus artifact Q3527241,
-- "Krull's principal ideal theorem": in a commutative Noetherian ring, every
-- prime ideal minimal over a principal ideal has height at most one. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Q3527241_krull_s_principal_ideal_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _and_
infixr 2 _or_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} P =
  P -> Bottom {a}

record _and_
  {a b : Level}
  (P : Set a)
  (Q : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : P
    second : Q

data _or_
  {a b : Level}
  (P : Set a)
  (Q : Set b) :
  Set (a ⊔ b) where

  left  : P -> P or Q
  right : Q -> P or Q

record CommutativeRing
  {a : Level}
  (R : Set a) :
  Set a where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR : R -> R

    add-associative :
      (x y z : R) ->
      addR (addR x y) z ≡ addR x (addR y z)
    add-commutative :
      (x y : R) ->
      addR x y ≡ addR y x
    add-zero-left :
      (x : R) ->
      addR zeroR x ≡ x
    add-zero-right :
      (x : R) ->
      addR x zeroR ≡ x
    add-inverse-left :
      (x : R) ->
      addR (negateR x) x ≡ zeroR
    add-inverse-right :
      (x : R) ->
      addR x (negateR x) ≡ zeroR

    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-commutative :
      (x y : R) ->
      multiplyR x y ≡ multiplyR y x
    multiply-one-left :
      (x : R) ->
      multiplyR oneR x ≡ x
    multiply-one-right :
      (x : R) ->
      multiplyR x oneR ≡ x
    distribute-left :
      (x y z : R) ->
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : R) ->
      multiplyR (addR x y) z ≡
      addR (multiplyR x z) (multiplyR y z)

record Ideal
  {a : Level}
  {R : Set a}
  (ring : CommutativeRing R) :
  Set (lsuc a) where

  field
    member : R -> Set a
    membership-propositional :
      (x : R) ->
      (u v : member x) ->
      u ≡ v
    contains-zero :
      member (CommutativeRing.zeroR ring)
    closed-under-addition :
      (x y : R) ->
      member x ->
      member y ->
      member (CommutativeRing.addR ring x y)
    closed-under-negation :
      (x : R) ->
      member x ->
      member (CommutativeRing.negateR ring x)
    absorbs-multiplication :
      (r x : R) ->
      member x ->
      member (CommutativeRing.multiplyR ring r x)

IdealIncludedIn :
  {a : Level} ->
  {R : Set a} ->
  {ring : CommutativeRing R} ->
  Ideal ring ->
  Ideal ring ->
  Set a
IdealIncludedIn {R = R} I J =
  (x : R) ->
  Ideal.member I x ->
  Ideal.member J x

StrictlyContained :
  {a : Level} ->
  {R : Set a} ->
  {ring : CommutativeRing R} ->
  Ideal ring ->
  Ideal ring ->
  Set a
StrictlyContained I J =
  IdealIncludedIn I J and
  Not (IdealIncludedIn J I)

data ContainsAll
  {a : Level}
  {R : Set a}
  {ring : CommutativeRing R}
  (I : Ideal ring) :
  List R ->
  Set a where

  contains-empty :
    ContainsAll I []

  contains-cons :
    {x : R} ->
    {xs : List R} ->
    Ideal.member I x ->
    ContainsAll I xs ->
    ContainsAll I (x ∷ xs)

GeneratesIdeal :
  {a : Level} ->
  {R : Set a} ->
  {ring : CommutativeRing R} ->
  List R ->
  Ideal ring ->
  Set (lsuc a)
GeneratesIdeal {ring = ring} generators I =
  ContainsAll I generators and
  ((J : Ideal ring) ->
    ContainsAll J generators ->
    IdealIncludedIn I J)

IsNoetherianRing :
  {a : Level} ->
  {R : Set a} ->
  (ring : CommutativeRing R) ->
  Set (lsuc a)
IsNoetherianRing {R = R} ring =
  (I : Ideal ring) ->
  Σ (List R)
    (λ generators ->
      GeneratesIdeal generators I)

IsPrincipal :
  {a : Level} ->
  {R : Set a} ->
  {ring : CommutativeRing R} ->
  Ideal ring ->
  Set (lsuc a)
IsPrincipal {R = R} I =
  Σ R
    (λ generator ->
      GeneratesIdeal (generator ∷ []) I)

IsPrime :
  {a : Level} ->
  {R : Set a} ->
  {ring : CommutativeRing R} ->
  Ideal ring ->
  Set a
IsPrime {R = R} {ring = ring} p =
  Not (Ideal.member p (CommutativeRing.oneR ring)) and
  ((x y : R) ->
    Ideal.member p (CommutativeRing.multiplyR ring x y) ->
    Ideal.member p x or
    Ideal.member p y)

MinimalPrimeOver :
  {a : Level} ->
  {R : Set a} ->
  {ring : CommutativeRing R} ->
  Ideal ring ->
  Ideal ring ->
  Set (lsuc a)
MinimalPrimeOver {ring = ring} I p =
  IsPrime p and
  (IdealIncludedIn I p and
   ((q : Ideal ring) ->
     IsPrime q ->
     IdealIncludedIn I q ->
     IdealIncludedIn q p ->
     IdealIncludedIn p q))

HeightAtMostOne :
  {a : Level} ->
  {R : Set a} ->
  {ring : CommutativeRing R} ->
  Ideal ring ->
  Set (lsuc a)
HeightAtMostOne {a} {ring = ring} p =
  (q r : Ideal ring) ->
  IsPrime q ->
  IsPrime r ->
  StrictlyContained r q ->
  StrictlyContained q p ->
  Bottom {a}

-- Lean: Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
krull-s-principal-ideal-theorem :
  (a : Level) ->
  Set (lsuc a)
krull-s-principal-ideal-theorem a =
  (R : Set a) ->
  (ring : CommutativeRing R) ->
  IsNoetherianRing ring ->
  (I : Ideal ring) ->
  IsPrincipal I ->
  (p : Ideal ring) ->
  MinimalPrimeOver I p ->
  HeightAtMostOne p
