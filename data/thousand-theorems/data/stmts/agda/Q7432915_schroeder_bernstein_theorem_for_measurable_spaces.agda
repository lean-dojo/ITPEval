-- Statement-only formalization of thousand-theorems corpus artifact Q7432915
-- (thousand-theorems__agda__Q7432915), "Schroeder–Bernstein theorem for
-- measurable spaces": measurable embeddings in both directions yield a
-- measurable equivalence. This file contains no proof.

{-# OPTIONS --safe #-}

module Q7432915_schroeder_bernstein_theorem_for_measurable_spaces where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

record Both
  {p q : Level}
  (P : Set p)
  (Q : Set q) :
  Set (p ⊔ q) where

  constructor both
  field
    first  : P
    second : Q

record Iff
  {p q : Level}
  (P : Set p)
  (Q : Set q) :
  Set (p ⊔ q) where

  constructor equivalence
  field
    forward  : P -> Q
    backward : Q -> P

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data Bottom {p : Level} : Set p where

Not :
  {p : Level} ->
  Set p ->
  Set p
Not {p} P =
  P -> Bottom {p}

Predicate :
  {a : Level} ->
  (p : Level) ->
  Set a ->
  Set (a ⊔ lsuc p)
Predicate p A =
  A -> Set p

Empty :
  {a p : Level} ->
  {A : Set a} ->
  Predicate p A
Empty _ =
  Bottom

Complement :
  {a p : Level} ->
  {A : Set a} ->
  Predicate p A ->
  Predicate p A
Complement S x =
  Not (S x)

CountableUnion :
  {a p : Level} ->
  {A : Set a} ->
  (Nat -> Predicate p A) ->
  Predicate p A
CountableUnion sets x =
  Exists Nat (\ n -> sets n x)

SamePredicate :
  {a p : Level} ->
  {A : Set a} ->
  Predicate p A ->
  Predicate p A ->
  Set (a ⊔ p)
SamePredicate {A = A} S T =
  (x : A) ->
  Iff (S x) (T x)

record SigmaAlgebra
  {a : Level}
  (p : Level)
  (A : Set a) :
  Set (a ⊔ lsuc p) where

  field
    measurable :
      Predicate p A ->
      Set p

    measurable-congruent :
      (S T : Predicate p A) ->
      SamePredicate S T ->
      measurable S ->
      measurable T

    measurable-empty :
      measurable Empty

    measurable-complement :
      (S : Predicate p A) ->
      measurable S ->
      measurable (Complement S)

    measurable-countable-union :
      (sets : Nat -> Predicate p A) ->
      ((n : Nat) -> measurable (sets n)) ->
      measurable (CountableUnion sets)

open SigmaAlgebra

Preimage :
  {a b p : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (A -> B) ->
  Predicate p B ->
  Predicate p A
Preimage f T x =
  T (f x)

Image :
  {a b p : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (A -> B) ->
  Predicate p A ->
  Predicate (a ⊔ b ⊔ p) B
Image {A = A} f S y =
  Exists A
    (\ x ->
      Both
        (S x)
        (f x ≡ y))

Injective :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (A -> B) ->
  Set (a ⊔ b)
Injective {A = A} f =
  (x y : A) ->
  f x ≡ f y ->
  x ≡ y

MeasurableFunction :
  {a b p : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  SigmaAlgebra p A ->
  SigmaAlgebra p B ->
  (A -> B) ->
  Set (b ⊔ lsuc p)
MeasurableFunction source target f =
  (T : Predicate _ _) ->
  measurable target T ->
  measurable source (Preimage f T)

record MeasurableEmbedding
  {a b : Level}
  (A : Set a)
  (B : Set b)
  (source : SigmaAlgebra (a ⊔ b) A)
  (target : SigmaAlgebra (a ⊔ b) B)
  (f : A -> B) :
  Set (lsuc (a ⊔ b)) where

  field
    injective :
      Injective f

    measurable-function :
      MeasurableFunction source target f

    measurable-image :
      (S : Predicate (a ⊔ b) A) ->
      measurable source S ->
      measurable target (Image f S)

record MeasurableEquivalence
  {a b : Level}
  (A : Set a)
  (B : Set b)
  (source : SigmaAlgebra (a ⊔ b) A)
  (target : SigmaAlgebra (a ⊔ b) B) :
  Set (lsuc (a ⊔ b)) where

  field
    to   : A -> B
    from : B -> A

    from-to :
      (x : A) ->
      from (to x) ≡ x

    to-from :
      (y : B) ->
      to (from y) ≡ y

    measurable-to :
      MeasurableFunction source target to

    measurable-from :
      MeasurableFunction target source from

schroeder-bernstein-theorem-for-measurable-spaces :
  {a b : Level} ->
  Set (lsuc (a ⊔ b))
schroeder-bernstein-theorem-for-measurable-spaces {a} {b} =
  (A : Set a) ->
  (B : Set b) ->
  (source : SigmaAlgebra (a ⊔ b) A) ->
  (target : SigmaAlgebra (a ⊔ b) B) ->
  (f : A -> B) ->
  (g : B -> A) ->
  MeasurableEmbedding A B source target f ->
  MeasurableEmbedding B A target source g ->
  MeasurableEquivalence A B source target
