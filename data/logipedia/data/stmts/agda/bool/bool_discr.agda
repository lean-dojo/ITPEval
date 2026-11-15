-- Statement-only formalization of Logipedia corpus artifact bool.bool_discr
-- (catalog title "bool.bool_discr"): equality of two Boolean values makes the
-- corresponding nested Boolean discrimination proposition hold. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module bool_discr where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

ChurchTrue : (level : Level) → Set (lsuc level)
ChurchTrue level =
  (P : Set level) → P → P

ChurchFalse : (level : Level) → Set (lsuc level)
ChurchFalse level =
  (P : Set level) → P

match-bool-type :
  {level : Level} →
  Set level →
  Set level →
  Bool →
  Set level
match-bool-type case-true case-false true =
  case-true
match-bool-type case-true case-false false =
  case-false

bool-discr : {level : Level} → Set (lsuc level)
bool-discr {level} =
  (x y : Bool) →
  x ≡ y →
  match-bool-type
    (match-bool-type (ChurchTrue level) (ChurchFalse level) y)
    (match-bool-type (ChurchFalse level) (ChurchTrue level) y)
    x
