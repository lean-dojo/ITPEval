-- Statement-only formalization of PutnamBench corpus artifact putnam_1971_b1:
-- an idempotent binary operation satisfying the cyclic law
-- (x * y) * z = (y * z) * x is associative and commutative.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)

infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

putnam-1971-b1 : Set1
putnam-1971-b1 =
  (S : Set) ->
  (op : S -> S -> S) ->
  ((x : S) -> op x x == x) ->
  ((x y z : S) -> op (op x y) z == op (op y z) x) ->
  ((x y z : S) -> op (op x y) z == op x (op y z))
  and
  ((x y : S) -> op x y == op y x)
