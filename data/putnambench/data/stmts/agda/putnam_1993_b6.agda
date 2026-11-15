-- Statement-only formalization of PutnamBench corpus artifact putnam_1993_b6:
-- three positive natural numbers can be transformed until one is zero by
-- repeatedly replacing an ordered pair x <= y with 2x and y - x. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _!=_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc i) =
  suc (toNat i)

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

lessOrEqualBool : Nat -> Nat -> Bool
lessOrEqualBool zero n =
  true
lessOrEqualBool (suc m) zero =
  false
lessOrEqualBool (suc m) (suc n) =
  lessOrEqualBool m n

If : Bool -> Set -> Set -> Set
If true when-true when-false =
  when-true
If false when-true when-false =
  when-false

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

Fin3 : Set
Fin3 =
  Fin three

State : Set
State =
  Fin3 -> Nat

StateEqual : State -> State -> Set
StateEqual A B =
  (i : Fin3) ->
  A i == B i

UpdateFunction : Set
UpdateFunction =
  Fin3 -> Fin3 -> State -> State

PairwiseDistinct : Fin3 -> Fin3 -> Fin3 -> Set
PairwiseDistinct i j k =
  i != j and i != k and j != k

UpdateAtPair :
  UpdateFunction ->
  Fin3 ->
  Fin3 ->
  Fin3 ->
  State ->
  Set
UpdateAtPair f i j k S' =
  ((f i j S') i == two * S' i)
  and
  ((f i j S') j == S' j - S' i)
  and
  ((f i j S') k == S' k)

UpdateSpecification : UpdateFunction -> Set
UpdateSpecification f =
  (i j k : Fin3) ->
  PairwiseDistinct i j k ->
  (S' : State) ->
  If
    (lessOrEqualBool (S' i) (S' j))
    (UpdateAtPair f i j k S')
    (StateEqual (f i j S') S')

FiniteTrajectory :
  State ->
  UpdateFunction ->
  Set
FiniteTrajectory S f =
  Exists (Nat -> State)
    (\ Ss ->
      Exists Nat
        (\ N ->
          StateEqual (Ss zero) S
          and
          Exists Fin3
            (\ i -> Ss N i == zero)
          and
          ((n : Fin N) ->
            Exists Fin3
              (\ i ->
                Exists Fin3
                  (\ j ->
                    i != j
                    and
                    StateEqual
                      (f i j (Ss (toNat n)))
                      (Ss (suc (toNat n))))))))

putnam-1993-b6 : Set
putnam-1993-b6 =
  (S : State) ->
  (f : UpdateFunction) ->
  ((i : Fin3) -> Positive (S i)) ->
  UpdateSpecification f ->
  FiniteTrajectory S f
