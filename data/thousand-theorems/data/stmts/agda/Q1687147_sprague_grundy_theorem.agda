-- Statement-only formalization of thousand-theorems corpus artifact Q1687147
-- (thousand-theorems__agda__Q1687147), "Sprague–Grundy theorem": every
-- impartial combinatorial game is equivalent to the Nim game indexed by its
-- minimum-excluded Grundy value. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1687147_sprague_grundy_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

data Bottom {p : Level} : Set p where

Not :
  {p : Level} ->
  Set p ->
  Set p
Not {p} proposition =
  proposition -> Bottom {p}

record Both
  {p q : Level}
  (left-proposition : Set p)
  (right-proposition : Set q) :
  Set (p ⊔ q) where

  constructor both
  field
    first  : left-proposition
    second : right-proposition

data Either
  {p q : Level}
  (left-proposition : Set p)
  (right-proposition : Set q) :
  Set (p ⊔ q) where

  left-case  : left-proposition -> Either left-proposition right-proposition
  right-case : right-proposition -> Either left-proposition right-proposition

record LogicalEquivalence
  {p q : Level}
  (left-proposition : Set p)
  (right-proposition : Set q) :
  Set (p ⊔ q) where

  constructor logically-equivalent
  field
    forward  : left-proposition -> right-proposition
    backward : right-proposition -> left-proposition

record Exists
  {a p : Level}
  (A : Set a)
  (property : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value     : A
    satisfies : property value

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

-- A universe-polymorphic inductive Conway game. The two arbitrary small
-- indexing types enumerate its left and right options.
data IGame (g : Level) : Set (lsuc g) where
  game :
    {LeftMoves RightMoves : Set g} ->
    (LeftMoves -> IGame g) ->
    (RightMoves -> IGame g) ->
    IGame g

data Player : Set where
  left right : Player

MoveType :
  {g : Level} ->
  Player ->
  IGame g ->
  Set g
MoveType left (game {LeftMoves} {RightMoves} left-options right-options) =
  LeftMoves
MoveType right (game {LeftMoves} {RightMoves} left-options right-options) =
  RightMoves

move :
  {g : Level} ->
  (player : Player) ->
  (x : IGame g) ->
  MoveType player x ->
  IGame g
move left (game left-options right-options) index =
  left-options index
move right (game left-options right-options) index =
  right-options index

negate :
  {g : Level} ->
  IGame g ->
  IGame g
negate (game left-options right-options) =
  game
    (\ right-index -> negate (right-options right-index))
    (\ left-index -> negate (left-options left-index))

Equivalent :
  {g r : Level} ->
  (IGame g -> IGame g -> Set r) ->
  IGame g ->
  IGame g ->
  Set r
Equivalent less-or-equal x y =
  Both
    (less-or-equal x y)
    (less-or-equal y x)

-- This bidirectional law is Conway's recursive definition of game order:
-- x <= y exactly when no left option of x is >= y and no right option of y
-- is <= x.
record ConwayOrder
  {g r : Level}
  (less-or-equal : IGame g -> IGame g -> Set r) :
  Set (lsuc g ⊔ r) where

  field
    characterization :
      (x y : IGame g) ->
      LogicalEquivalence
        (less-or-equal x y)
        (Both
          ((left-index : MoveType left x) ->
            Not (less-or-equal y (move left x left-index)))
          ((right-index : MoveType right y) ->
            Not (less-or-equal (move right y right-index) x)))

-- Impartiality is hereditary and identifies a game with its conjugate, as in
-- the source IGame.Impartial structure.
Impartial :
  {g r : Level} ->
  (IGame g -> IGame g -> Set r) ->
  IGame g ->
  Set (lsuc g ⊔ r)
Impartial less-or-equal
  x@(game {LeftMoves} {RightMoves} left-options right-options) =
  Both
    (Equivalent less-or-equal x (negate x))
    (Both
      ((left-index : LeftMoves) ->
        Impartial less-or-equal (left-options left-index))
      ((right-index : RightMoves) ->
        Impartial less-or-equal (right-options right-index)))

data Accessible
  {a r : Level}
  {A : Set a}
  (strictly-less : A -> A -> Set r)
  (x : A) :
  Set (a ⊔ r) where

  accessible :
    ((y : A) ->
      strictly-less y x ->
      Accessible strictly-less y) ->
    Accessible strictly-less x

WellFounded :
  {a r : Level} ->
  {A : Set a} ->
  (A -> A -> Set r) ->
  Set (a ⊔ r)
WellFounded {A = A} strictly-less =
  (x : A) ->
  Accessible strictly-less x

-- Nimbers form a strict linear well-order. This record presents the fixed
-- source Nimber type up to an order-preserving change of representation.
record StrictWellOrder
  {n s : Level}
  (Nimber : Set n)
  (strictly-less : Nimber -> Nimber -> Set s) :
  Set (lsuc n ⊔ s) where

  field
    irreflexive :
      (x : Nimber) ->
      Not (strictly-less x x)
    transitive :
      (x y z : Nimber) ->
      strictly-less x y ->
      strictly-less y z ->
      strictly-less x z
    trichotomy :
      (x y : Nimber) ->
      Either
        (strictly-less x y)
        (Either (x == y) (strictly-less y x))
    well-founded :
      WellFounded strictly-less

record Below
  {n s : Level}
  {Nimber : Set n}
  (strictly-less : Nimber -> Nimber -> Set s)
  (upper : Nimber) :
  Set (n ⊔ s) where

  constructor below
  field
    value   : Nimber
    smaller : strictly-less value upper

-- A Nim game indexed by o has, for either player, exactly one option
-- corresponding to every nimber strictly below o, and that option is the
-- recursively indexed Nim game.
record NimLaw
  {g n s : Level}
  {Nimber : Set n}
  (strictly-less : Nimber -> Nimber -> Set s)
  (nim : Nimber -> IGame g) :
  Set (lsuc g ⊔ n ⊔ s) where

  field
    move-bijection :
      (player : Player) ->
      (o : Nimber) ->
      Bijection
        (MoveType player (nim o))
        (Below strictly-less o)
    move-is-nim :
      (player : Player) ->
      (o : Nimber) ->
      (index : MoveType player (nim o)) ->
      move player (nim o) index
        ==
      nim
        (Below.value
          (Bijection.to (move-bijection player o) index))

-- These two clauses are the minimum-excluded definition of the right Grundy
-- value: the value itself is absent from the option values, while every
-- strictly smaller nimber occurs.
record GrundyLaw
  {g n s : Level}
  {Nimber : Set n}
  (strictly-less : Nimber -> Nimber -> Set s)
  (grundy : IGame g -> Nimber) :
  Set (lsuc g ⊔ n ⊔ s) where

  field
    excluded :
      (x : IGame g) ->
      (index : MoveType right x) ->
      Not
        (grundy (move right x index)
          ==
         grundy x)
    covers-smaller :
      (x : IGame g) ->
      (o : Nimber) ->
      strictly-less o (grundy x) ->
      Exists
        (MoveType right x)
        (\ index ->
          grundy (move right x index) == o)

sprague-grundy-theorem :
  {g n r s : Level} ->
  (Nimber : Set n) ->
  (less-or-equal : IGame g -> IGame g -> Set r) ->
  ConwayOrder less-or-equal ->
  (strictly-less : Nimber -> Nimber -> Set s) ->
  StrictWellOrder Nimber strictly-less ->
  (nim : Nimber -> IGame g) ->
  NimLaw strictly-less nim ->
  (grundy : IGame g -> Nimber) ->
  GrundyLaw strictly-less grundy ->
  Set (lsuc g ⊔ r)
sprague-grundy-theorem
  Nimber
  less-or-equal
  conway-order
  strictly-less
  nimber-order
  nim
  nim-law
  grundy
  grundy-law =
  (x : IGame _) ->
  Impartial less-or-equal x ->
  Equivalent less-or-equal (nim (grundy x)) x
