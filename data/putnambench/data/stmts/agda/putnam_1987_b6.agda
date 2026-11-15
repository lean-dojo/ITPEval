-- Statement-only formalization of PutnamBench corpus artifact putnam_1987_b6:
-- in a finite field of odd prime-square order, the elements of a sign-choice
-- set that are doubles of elements of the same set have even cardinality.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_ _xor_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not proposition =
  proposition -> Bottom

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

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

data _xor_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  only-left  : A -> Not B -> A xor B
  only-right : Not A -> B -> A xor B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

record HasCardinality
  {a : Level}
  {A : Set a}
  (member : A -> Set a)
  (cardinality : Nat) :
  Set a where

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
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record Field
  {a : Level}
  (F : Set a) :
  Set (lsuc a) where

  field
    zeroF oneF : F
    add multiply : F -> F -> F
    negate inverse : F -> F

    one-not-zero :
      oneF != zeroF

    add-commutative :
      (x y : F) -> add x y == add y x
    add-associative :
      (x y z : F) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : F) -> add x zeroF == x
    add-inverse :
      (x : F) -> add x (negate x) == zeroF

    multiply-commutative :
      (x y : F) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : F) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : F) -> multiply x oneF == x
    multiply-zero :
      (x : F) -> multiply x zeroF == zeroF
    distribute :
      (x y z : F) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroF == zeroF
    multiply-inverse :
      (x : F) ->
      x != zeroF ->
      multiply x (inverse x) == oneF

open Field

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

half : Nat -> Nat
half zero =
  zero
half (suc zero) =
  zero
half (suc (suc n)) =
  suc (half n)

Odd : Nat -> Set
Odd n =
  Exists Nat
    (\ k -> n == suc (two * k))

Divides : Nat -> Nat -> Set
Divides divisor n =
  Exists Nat
    (\ quotient -> n == divisor * quotient)

Prime : Nat -> Set
Prime n =
  two <=N n
  and
  ((divisor : Nat) ->
    Divides divisor n ->
    divisor == one or divisor == n)

EvenCardinality :
  {a : Level} ->
  {A : Set a} ->
  (A -> Set a) ->
  Set a
EvenCardinality member =
  Exists Nat
    (\ k -> HasCardinality member (two * k))

module Putnam1987B6Statement
  {a : Level}
  {F : Set a}
  (algebra : Field F) where

  intersectionWithDoubles :
    (F -> Set a) ->
    F ->
    Set a
  intersectionWithDoubles member x =
    member x
    and
    Exists F
      (\ y ->
        member y
        and
        x == add algebra y y)

  proposition : Set (lsuc a)
  proposition =
    (p : Nat) ->
    Odd p and Prime p ->
    Bijection F (Fin (p * p)) ->
    (S : F -> Set a) ->
    ((x : F) ->
      S x ->
      x != zeroF algebra) ->
    HasCardinality S (half ((p * p) - one)) ->
    ((x : F) ->
      x != zeroF algebra ->
      S x xor S (negate algebra x)) ->
    EvenCardinality (intersectionWithDoubles S)

putnam-1987-b6 :
  {a : Level} ->
  Set (lsuc a)
putnam-1987-b6 {a} =
  (F : Set a) ->
  (algebra : Field F) ->
  Putnam1987B6Statement.proposition algebra
