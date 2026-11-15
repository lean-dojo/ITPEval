-- Statement-only formalization of Logipedia corpus artifact bool.andb_true_l
-- (catalog title "bool.andb_true_l"): if Boolean conjunction is true, its
-- left operand is true. This file contains no proof.

{-# OPTIONS --safe #-}

module andb_true_l where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

andb : Bool → Bool → Bool
andb true b2 =
  b2
andb false b2 =
  false

andb-true-l : Set
andb-true-l =
  (b1 b2 : Bool) →
  andb b1 b2 ≡ true →
  b1 ≡ true
