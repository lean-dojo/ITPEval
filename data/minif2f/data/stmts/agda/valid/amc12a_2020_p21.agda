-- Statement-only formalization of miniF2F valid problem amc12a_2020_p21. This file contains no
-- proof.

module amc12a-2020-p21 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _∈_
infix 2 _↔_

data ⊥ : Set where

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

data NoDuplicates {A : Set} : List A → Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

record Divides (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

record IsGCD (a b gcd : Nat) : Set where
  field
    divides-left :
      Divides gcd a
    divides-right :
      Divides gcd b
    greatest :
      (d : Nat) →
      Divides d a →
      Divides d b →
      Divides d gcd

record IsLCM (a b lcm : Nat) : Set where
  field
    left-divides :
      Divides a lcm
    right-divides :
      Divides b lcm
    least :
      (m : Nat) →
      Divides a m →
      Divides b m →
      Divides lcm m

record SatisfiesCondition (n : Nat) : Set where
  field
    divisible-by-five :
      Divides 5 n
    gcd-value :
      Nat
    lcm-value :
      Nat
    gcd-specification :
      IsGCD (factorial 10) n gcd-value
    lcm-specification :
      IsLCM (factorial 5) n lcm-value
    lcm-gcd-equation :
      lcm-value ≡ 5 * gcd-value

record ExactSolutionList : Set where
  field
    solutions :
      List Nat
    no-duplicates :
      NoDuplicates solutions
    exact-membership :
      (n : Nat) →
      (n ∈ solutions) ↔ SatisfiesCondition n
    cardinality :
      length solutions ≡ 48

amc12a-2020-p21 : Set
amc12a-2020-p21 = ExactSolutionList
