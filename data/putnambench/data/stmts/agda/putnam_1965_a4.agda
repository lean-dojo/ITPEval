-- Statement-only formalization of PutnamBench corpus artifact putnam_1965_a4:
-- for finite nonempty sets of girls and boys, if every girl dances with some
-- boy but no boy dances with every girl, then two girls and two boys exhibit
-- the specified crossed dance and non-dance pattern. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; suc)

infixr 3 _and_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

record Top : Set where
  constructor truth

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
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size : Nat
    enumerate : Fin size -> A
    enumeration-complete :
      (x : A) ->
      Exists (Fin size) (\ i -> enumerate i == x)
    enumeration-injective :
      (i j : Fin size) ->
      enumerate i == enumerate j ->
      i == j

Nonempty :
  {a : Level} ->
  Set a ->
  Set a
Nonempty A =
  Exists A (\ _ -> Top)

putnam-1965-a4 :
  {g b p : Level} ->
  Set (lsuc (g ⊔ b ⊔ p))
putnam-1965-a4 {g} {b} {p} =
  (G : Set g) ->
  (B : Set b) ->
  Finite G ->
  Finite B ->
  Nonempty G ->
  Nonempty B ->
  (dances : G -> B -> Set p) ->
  (Not
    (Exists B
      (\ boy ->
        (girl : G) ->
        dances girl boy))
   and
   ((girl : G) ->
     Exists B
       (\ boy ->
         dances girl boy))) ->
  Exists G
    (\ girl-g ->
      Exists G
        (\ girl-h ->
          Exists B
            (\ boy-b ->
              Exists B
                (\ boy-c ->
                  dances girl-g boy-b
                  and dances girl-h boy-c
                  and Not (dances girl-h boy-b)
                  and Not (dances girl-g boy-c)))))
