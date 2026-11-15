-- Statement-only formalization of PutnamBench corpus artifact putnam_1988_a6:
-- a finite-dimensional linear endomorphism with n+1 eigenvectors, every n of
-- which are linearly independent, is scalar multiplication. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

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

Injective :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (A -> B) ->
  Set (a ⊔ b)
Injective function =
  (x y : _) ->
  function x == function y ->
  x == y

record HasCardinality
  {a p : Level}
  {A : Set a}
  (member : A -> Set p)
  (cardinality : Nat) :
  Set (a ⊔ p) where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      Injective enumerate

record Field
  {f : Level}
  (F : Set f) :
  Set (lsuc f) where

  field
    zeroF oneF : F
    addF multiplyF : F -> F -> F
    negateF inverseF : F -> F

    one-not-zero :
      oneF != zeroF

    add-commutative :
      (x y : F) ->
      addF x y == addF y x
    add-associative :
      (x y z : F) ->
      addF (addF x y) z == addF x (addF y z)
    add-zero :
      (x : F) ->
      addF x zeroF == x
    add-inverse :
      (x : F) ->
      addF x (negateF x) == zeroF

    multiply-commutative :
      (x y : F) ->
      multiplyF x y == multiplyF y x
    multiply-associative :
      (x y z : F) ->
      multiplyF (multiplyF x y) z ==
      multiplyF x (multiplyF y z)
    multiply-one :
      (x : F) ->
      multiplyF x oneF == x
    distribute :
      (x y z : F) ->
      multiplyF x (addF y z) ==
      addF (multiplyF x y) (multiplyF x z)
    multiply-inverse :
      (x : F) ->
      x != zeroF ->
      multiplyF x (inverseF x) == oneF

open Field

record VectorSpace
  {f v : Level}
  {F : Set f}
  (fieldStructure : Field F)
  (V : Set v) :
  Set (lsuc (f ⊔ v)) where

  field
    zeroV : V
    addV : V -> V -> V
    negateV : V -> V
    smul : F -> V -> V

    addV-commutative :
      (x y : V) ->
      addV x y == addV y x
    addV-associative :
      (x y z : V) ->
      addV (addV x y) z == addV x (addV y z)
    addV-zero :
      (x : V) ->
      addV x zeroV == x
    addV-inverse :
      (x : V) ->
      addV x (negateV x) == zeroV

    smul-addV :
      (a : F) ->
      (x y : V) ->
      smul a (addV x y) ==
      addV (smul a x) (smul a y)
    addF-smul :
      (a b : F) ->
      (x : V) ->
      smul (addF fieldStructure a b) x ==
      addV (smul a x) (smul b x)
    multiplyF-smul :
      (a b : F) ->
      (x : V) ->
      smul (multiplyF fieldStructure a b) x ==
      smul a (smul b x)
    oneF-smul :
      (x : V) ->
      smul (oneF fieldStructure) x == x

open VectorSpace

record Endomorphism
  {f v : Level}
  {F : Set f}
  {V : Set v}
  (fieldStructure : Field F)
  (space : VectorSpace fieldStructure V) :
  Set (lsuc (f ⊔ v)) where

  field
    apply : V -> V
    map-add :
      (x y : V) ->
      apply (addV space x y) ==
      addV space (apply x) (apply y)
    map-smul :
      (a : F) ->
      (x : V) ->
      apply (smul space a x) ==
      smul space a (apply x)

open Endomorphism

sumFin :
  {f v : Level} ->
  {F : Set f} ->
  {V : Set v} ->
  (fieldStructure : Field F) ->
  (space : VectorSpace fieldStructure V) ->
  {n : Nat} ->
  (Fin n -> V) ->
  V
sumFin fieldStructure space {zero} terms =
  zeroV space
sumFin fieldStructure space {suc n} terms =
  addV space
    (terms fzero)
    (sumFin fieldStructure space
      (\ index -> terms (fsuc index)))

module Putnam1988A6Statement
  {f v p : Level}
  {F : Set f}
  {V : Set v}
  (fieldStructure : Field F)
  (space : VectorSpace fieldStructure V) where

  linearCombination :
    {n : Nat} ->
    (Fin n -> F) ->
    (Fin n -> V) ->
    V
  linearCombination coefficients vectors =
    sumFin fieldStructure space
      (\ index ->
        smul space
          (coefficients index)
          (vectors index))

  LinearIndependent :
    {n : Nat} ->
    (Fin n -> V) ->
    Set (f ⊔ v)
  LinearIndependent vectors =
    (coefficients : Fin _ -> F) ->
    linearCombination coefficients vectors == zeroV space ->
    (index : Fin _) ->
    coefficients index == zeroF fieldStructure

  Spans :
    {n : Nat} ->
    (Fin n -> V) ->
    Set (f ⊔ v)
  Spans vectors =
    (x : V) ->
    Exists (Fin _ -> F)
      (\ coefficients ->
        linearCombination coefficients vectors == x)

  HasDimension :
    Nat ->
    Set (f ⊔ v)
  HasDimension n =
    Exists (Fin n -> V)
      (\ basis ->
        LinearIndependent basis
        and
        Spans basis)

  Eigenvector :
    Endomorphism fieldStructure space ->
    V ->
    Set (f ⊔ v)
  Eigenvector A vector =
    vector != zeroV space
    and
    Exists F
      (\ eigenvalue ->
        apply A vector ==
        smul space eigenvalue vector)

  EveryNIndependent :
    (n : Nat) ->
    (V -> Set p) ->
    Set (f ⊔ v ⊔ p)
  EveryNIndependent n member =
    (selection : Fin n -> V) ->
    ((index : Fin n) -> member (selection index)) ->
    Injective selection ->
    LinearIndependent selection

  ScalarEndomorphism :
    Endomorphism fieldStructure space ->
    F ->
    Set v
  ScalarEndomorphism A scalar =
    (x : V) ->
    apply A x == smul space scalar x

  proposition :
    Set (lsuc (f ⊔ v ⊔ p))
  proposition =
    (n : Nat) ->
    (A : Endomorphism fieldStructure space) ->
    (eigenvectors : V -> Set p) ->
    HasDimension n ->
    ((vector : V) ->
      eigenvectors vector ->
      Eigenvector A vector) ->
    HasCardinality eigenvectors (suc n) ->
    EveryNIndependent n eigenvectors ->
    Exists F (ScalarEndomorphism A)

putnam-1988-a6 :
  {f v p : Level} ->
  Set (lsuc (f ⊔ v ⊔ p))
putnam-1988-a6 {f} {v} {p} =
  (F : Set f) ->
  (V : Set v) ->
  (fieldStructure : Field F) ->
  (space : VectorSpace fieldStructure V) ->
  Putnam1988A6Statement.proposition {p = p} fieldStructure space
