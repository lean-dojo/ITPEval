-- Statement-only formalization of "The Friendship Theorem" from Hundred Theorems item 083. This
-- file contains no proof.

module FriendshipTheorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; suc)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

data Bottom : Set where

Not : Set -> Set
Not proposition = proposition -> Bottom

NotEqual : {A : Set} -> A -> A -> Set
NotEqual left right = Not (left == right)

record Nonempty (A : Set) : Set where
  constructor inhabited
  field
    element : A

record _and_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

infixr 3 _and_

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    exists-value : A
    exists-property : P exists-value

record ExistsUnique (A : Set) (P : A -> Set) : Set where
  constructor unique-witness
  field
    unique-value : A
    unique-property : P unique-value
    uniqueness : (other : A) -> P other -> other == unique-value

friendship-theorem : Set₁
friendship-theorem =
  (number-of-vertices : Nat) ->
  (friend : Fin number-of-vertices -> Fin number-of-vertices -> Set) ->
  Nonempty (Fin number-of-vertices) ->
  ((vertex : Fin number-of-vertices) -> Not (friend vertex vertex)) ->
  ((left right : Fin number-of-vertices) ->
    friend left right ->
    friend right left) ->
  ((left right : Fin number-of-vertices) ->
    NotEqual left right ->
    ExistsUnique (Fin number-of-vertices)
      (\ common ->
        friend left common and friend right common)) ->
  Exists (Fin number-of-vertices)
    (\ politician ->
      (other : Fin number-of-vertices) ->
      NotEqual other politician ->
      friend politician other)
