-- Statement-only formalization of thousand-theorems corpus artifact Q1047749,
-- "Turán's theorem": for positive r, a finite simple graph is r-Turán-maximal
-- exactly when it is isomorphic to the canonical residue-class Turán graph.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1047749_tur_n_s_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; mod-helper)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _×_
infix 2 _↔_

data Bottom : Set where

Not :
  {a : Level} →
  Set a →
  Set a
Not proposition =
  proposition → Bottom

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record _↔_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor iff
  field
    forward  : A → B
    backward : B → A

data Positive : Nat → Set where
  positive : {n : Nat} → Positive (suc n)

data _≤_ : Nat → Nat → Set where
  zero≤    : {n : Nat} → zero ≤ n
  suc≤suc  : {m n : Nat} → m ≤ n → suc m ≤ suc n

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

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

FinitePresentation :
  {a : Level} →
  Set a →
  Set a
FinitePresentation A =
  Σ Nat (λ cardinality → Bijection A (Fin cardinality))

record SimpleGraph
  {a : Level}
  (V : Set a) :
  Set a where

  field
    adjacent  : V → V → Bool
    loopless  : (v : V) → adjacent v v ≡ false
    symmetric : (v w : V) → adjacent v w ≡ adjacent w v

open Bijection
open SimpleGraph

notBool : Bool → Bool
notBool true =
  false
notBool false =
  true

andBool : Bool → Bool → Bool
andBool true right =
  right
andBool false right =
  false

indicator : Bool → Nat
indicator true =
  suc zero
indicator false =
  zero

finLess :
  {n : Nat} →
  Fin n →
  Fin n →
  Bool
finLess fzero fzero =
  false
finLess fzero (fsuc j) =
  true
finLess (fsuc i) fzero =
  false
finLess (fsuc i) (fsuc j) =
  finLess i j

finToNat :
  {n : Nat} →
  Fin n →
  Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

natEqual :
  Nat →
  Nat →
  Bool
natEqual zero zero =
  true
natEqual zero (suc right) =
  false
natEqual (suc left) zero =
  false
natEqual (suc left) (suc right) =
  natEqual left right

naturalMod :
  Nat →
  Nat →
  Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

countFin :
  {n : Nat} →
  (Fin n → Bool) →
  Nat
countFin {zero} predicate =
  zero
countFin {suc n} predicate =
  indicator (predicate fzero) +
  countFin (λ i → predicate (fsuc i))

sumFin :
  {n : Nat} →
  (Fin n → Nat) →
  Nat
sumFin {zero} term =
  zero
sumFin {suc n} term =
  term fzero +
  sumFin (λ i → term (fsuc i))

cardinality :
  {a : Level} →
  {V : Set a} →
  FinitePresentation V →
  Nat
cardinality finite =
  Σ.fst finite

enumeration :
  {a : Level} →
  {V : Set a} →
  (finite : FinitePresentation V) →
  Bijection V (Fin (cardinality finite))
enumeration finite =
  Σ.snd finite

edgeCount :
  {a : Level} →
  {V : Set a} →
  FinitePresentation V →
  SimpleGraph V →
  Nat
edgeCount finite graph =
  sumFin
    (λ i →
      countFin
        (λ j →
          andBool
            (finLess i j)
            (adjacent graph
              (from (enumeration finite) i)
              (from (enumeration finite) j))))

Injective :
  {a b : Level} →
  {A : Set a} →
  {B : Set b} →
  (A → B) →
  Set (a ⊔ b)
Injective {A = A} function =
  (x y : A) →
  function x ≡ function y →
  x ≡ y

PairwiseAdjacent :
  {a : Level} →
  {V : Set a} →
  {k : Nat} →
  SimpleGraph V →
  (Fin k → V) →
  Set
PairwiseAdjacent graph vertices =
  (i j : Fin _) →
  Not (i ≡ j) →
  adjacent graph (vertices i) (vertices j) ≡ true

CliqueEmbedding :
  {a : Level} →
  {V : Set a} →
  SimpleGraph V →
  Nat →
  Set a
CliqueEmbedding {V = V} graph k =
  Σ (Fin k → V)
    (λ vertices →
      Injective vertices ×
      PairwiseAdjacent graph vertices)

CliqueFree :
  {a : Level} →
  {V : Set a} →
  SimpleGraph V →
  Nat →
  Set a
CliqueFree graph k =
  Not (CliqueEmbedding graph k)

record IsTuranMaximal
  {a : Level}
  {V : Set a}
  (finite : FinitePresentation V)
  (graph : SimpleGraph V)
  (r : Nat) :
  Set a where

  field
    clique-free :
      CliqueFree graph (suc r)
    maximal :
      (other : SimpleGraph V) →
      CliqueFree other (suc r) →
      edgeCount finite other ≤ edgeCount finite graph

turanAdjacent :
  {n : Nat} →
  Nat →
  Fin n →
  Fin n →
  Bool
turanAdjacent r left right =
  notBool
    (natEqual
      (naturalMod (finToNat left) r)
      (naturalMod (finToNat right) r))

record IsomorphicToTuranGraph
  {a : Level}
  {V : Set a}
  (finite : FinitePresentation V)
  (graph : SimpleGraph V)
  (r : Nat) :
  Set a where

  field
    relabel :
      Bijection V (Fin (cardinality finite))
    adjacency-equivalence :
      (v w : V) →
      adjacent graph v w ≡
      turanAdjacent r (to relabel v) (to relabel w)

turan-s-theorem :
  {a : Level} →
  Set (lsuc a)
turan-s-theorem {a} =
  (V : Set a) →
  (finite : FinitePresentation V) →
  (graph : SimpleGraph V) →
  (r : Nat) →
  Positive r →
  IsTuranMaximal finite graph r
    ↔
  IsomorphicToTuranGraph finite graph r
