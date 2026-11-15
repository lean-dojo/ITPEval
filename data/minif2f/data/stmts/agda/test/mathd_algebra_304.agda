-- Statement-only formalization of miniF2F test problem mathd_algebra_304:
-- the natural-number equality stating that the square of 91 is 8281. This
-- file contains no proof.

module mathd-algebra-304 where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Equality using (_≡_)

mathd-algebra-304 : Set
mathd-algebra-304 = (91 * 91) ≡ 8281
