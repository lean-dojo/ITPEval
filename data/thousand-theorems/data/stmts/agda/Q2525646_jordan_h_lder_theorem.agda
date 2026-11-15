-- Statement-only formalization of thousand-theorems corpus artifact Q2525646
-- (thousand-theorems__agda__Q2525646), "Jordan–Hölder theorem": composition
-- series with the same least and greatest elements are equivalent in any
-- Jordan–Hölder lattice. This file contains no proof.

{-# OPTIONS --safe #-}

module Q2525646_jordan_h_lder_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
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

record Both
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record Pair
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor _,_
  field
    left  : A
    right : B

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

castSucc :
  {n : Nat} ->
  Fin n ->
  Fin (suc n)
castSucc {zero} ()
castSucc {suc n} fzero =
  fzero
castSucc {suc n} (fsuc i) =
  fsuc (castSucc i)

lastIndex :
  (n : Nat) ->
  Fin (suc n)
lastIndex zero =
  fzero
lastIndex (suc n) =
  fsuc (lastIndex n)

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to      : A -> B
    from    : B -> A
    from-to : (x : A) -> from (to x) == x
    to-from : (y : B) -> to (from y) == y

record Lattice
  {a : Level}
  (X : Set a) :
  Set (lsuc a) where

  field
    le  : X -> X -> Set a
    inf : X -> X -> X
    sup : X -> X -> X

    le-propositional :
      (x y : X) ->
      (p q : le x y) ->
      p == q

    le-refl :
      (x : X) ->
      le x x
    le-trans :
      (x y z : X) ->
      le x y ->
      le y z ->
      le x z
    le-antisym :
      (x y : X) ->
      le x y ->
      le y x ->
      x == y

    inf-le-left :
      (x y : X) ->
      le (inf x y) x
    inf-le-right :
      (x y : X) ->
      le (inf x y) y
    le-inf :
      (x y z : X) ->
      le x y ->
      le x z ->
      le x (inf y z)

    le-sup-left :
      (x y : X) ->
      le x (sup x y)
    le-sup-right :
      (x y : X) ->
      le y (sup x y)
    sup-le :
      (x y z : X) ->
      le x z ->
      le y z ->
      le (sup x y) z

StrictLess :
  {a : Level} ->
  {X : Set a} ->
  Lattice X ->
  X ->
  X ->
  Set a
StrictLess lattice x y =
  Both
    (Lattice.le lattice x y)
    (Not (x == y))

record JordanHolderLattice
  {a : Level}
  {X : Set a}
  (lattice : Lattice X) :
  Set (lsuc a) where

  open Lattice lattice

  field
    IsMaximal : X -> X -> Set a

    isMaximal-propositional :
      (x y : X) ->
      (p q : IsMaximal x y) ->
      p == q

    lt-of-isMaximal :
      {x y : X} ->
      IsMaximal x y ->
      StrictLess lattice x y

    sup-eq-of-isMaximal :
      {x y z : X} ->
      IsMaximal x z ->
      IsMaximal y z ->
      Not (x == y) ->
      sup x y == z

    isMaximal-inf-left-of-isMaximal-sup :
      {x y : X} ->
      IsMaximal x (sup x y) ->
      IsMaximal y (sup x y) ->
      IsMaximal (inf x y) x

    Iso :
      Pair X X ->
      Pair X X ->
      Set a

    iso-propositional :
      (p q : Pair X X) ->
      (h k : Iso p q) ->
      h == k

    iso-symmetric :
      {p q : Pair X X} ->
      Iso p q ->
      Iso q p

    iso-transitive :
      {p q r : Pair X X} ->
      Iso p q ->
      Iso q r ->
      Iso p r

    second-isomorphism :
      {x y : X} ->
      IsMaximal x (sup x y) ->
      Iso
        (x , sup x y)
        (inf x y , y)

record CompositionSeries
  {a : Level}
  {X : Set a}
  {lattice : Lattice X}
  (structure : JordanHolderLattice lattice) :
  Set a where

  field
    length : Nat
    term   : Fin (suc length) -> X
    step   :
      (i : Fin length) ->
      JordanHolderLattice.IsMaximal structure
        (term (castSucc i))
        (term (fsuc i))

head :
  {a : Level} ->
  {X : Set a} ->
  {lattice : Lattice X} ->
  {structure : JordanHolderLattice lattice} ->
  CompositionSeries structure ->
  X
head series =
  CompositionSeries.term series fzero

last :
  {a : Level} ->
  {X : Set a} ->
  {lattice : Lattice X} ->
  {structure : JordanHolderLattice lattice} ->
  (series : CompositionSeries structure) ->
  X
last series =
  CompositionSeries.term series
    (lastIndex (CompositionSeries.length series))

Equivalent :
  {a : Level} ->
  {X : Set a} ->
  {lattice : Lattice X} ->
  {structure : JordanHolderLattice lattice} ->
  CompositionSeries structure ->
  CompositionSeries structure ->
  Set a
Equivalent {structure = structure} left-series right-series =
  Σ
    (Bijection
      (Fin (CompositionSeries.length left-series))
      (Fin (CompositionSeries.length right-series)))
    (\ factor-bijection ->
      (i : Fin (CompositionSeries.length left-series)) ->
      JordanHolderLattice.Iso structure
        (CompositionSeries.term left-series (castSucc i) ,
         CompositionSeries.term left-series (fsuc i))
        (CompositionSeries.term right-series
           (castSucc (Bijection.to factor-bijection i)) ,
         CompositionSeries.term right-series
           (fsuc (Bijection.to factor-bijection i))))

-- Lean: CompositionSeries.jordan_holder
jordan-holder :
  (a : Level) ->
  Set (lsuc a)
jordan-holder a =
  {X : Set a} ->
  (lattice : Lattice X) ->
  (structure : JordanHolderLattice lattice) ->
  (left-series right-series : CompositionSeries structure) ->
  head left-series == head right-series ->
  last left-series == last right-series ->
  Equivalent left-series right-series
