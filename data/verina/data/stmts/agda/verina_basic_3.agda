-- Statement-only formalization of VERINA corpus artifact verina_basic_3,
-- catalog title "isDivisibleBy11": a total integer program returns true
-- exactly when its input is an integer multiple of eleven, with the executable
-- remainder test connected to its two-direction correctness contract.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic3 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; mod-helper)

infixr 3 _∧_

record Top : Set where
  constructor top

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data Exists {A : Set} (P : A → Set) : Set where
  witness : (x : A) → P x → Exists P

data IsTrue : Bool → Set where
  true-witness : IsTrue true

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

eleven : Nat
eleven =
  suc
    (suc
      (suc
        (suc
          (suc
            (suc
              (suc
                (suc
                  (suc
                    (suc
                      (suc zero))))))))))

zeroInt : Int
zeroInt = pos zero

elevenInt : Int
elevenInt = pos eleven

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

intMultiply : Int → Int → Int
intMultiply (pos m) (pos n) = pos (m * n)
intMultiply (pos m) (negsuc n) = negative (m * suc n)
intMultiply (negsuc m) (pos n) = negative (suc m * n)
intMultiply (negsuc m) (negsuc n) = pos (suc m * suc n)

-- Lean's remainder modulo positive eleven is always in [0, 11).
moduloByEleven : Int → Int
moduloByEleven (pos n) =
  pos (naturalMod n eleven)
moduloByEleven (negsuc n) with naturalMod (suc n) eleven
... | zero = zeroInt
... | suc remainder =
  pos (natSubtract eleven (suc remainder))

isDivisibleBy11-precond : Int → Set
isDivisibleBy11-precond n = Top

isDivisibleBy11 :
  (n : Int) →
  isDivisibleBy11-precond n →
  Bool
isDivisibleBy11 n h-precond =
  intEqual (moduloByEleven n) zeroInt

isDivisibleBy11-postcond :
  (n : Int) →
  (result : Bool) →
  isDivisibleBy11-precond n →
  Set
isDivisibleBy11-postcond n result h-precond =
  (IsTrue result →
    Exists (λ k → n ≡ intMultiply elevenInt k)) ∧
  (Not (IsTrue result) →
    (k : Int) →
    Not (n ≡ intMultiply elevenInt k))

isDivisibleBy11-spec-satisfied : Set
isDivisibleBy11-spec-satisfied =
  (n : Int) →
  (h-precond : isDivisibleBy11-precond n) →
  isDivisibleBy11-postcond
    n
    (isDivisibleBy11 n h-precond)
    h-precond
