-- Statement-only formalization of PutnamBench corpus artifact
-- putnambench__agda__putnam_1984_a6: last nonzero factorial digits on sums
-- of distinct powers of five depend only on the exponent sum, and the induced
-- function has least positive period four from index one. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<N_ _<=N_
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

data _<N_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero <N suc n
  succ<succ : {m n : Nat} -> m <N n -> suc m <N suc n

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

oneN : Nat
oneN =
  suc zero

fourN : Nat
fourN =
  4

fiveN : Nat
fiveN =
  5

tenN : Nat
tenN =
  10

Positive : Nat -> Set
Positive n =
  zero <N n

power : Nat -> Nat -> Nat
power base zero =
  oneN
power base (suc exponent) =
  base * power base exponent

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

sumFin : {n : Nat} -> (Fin n -> Nat) -> Nat
sumFin {zero} terms =
  zero
sumFin {suc n} terms =
  terms fzero + sumFin (\ i -> terms (fsuc i))

InjectiveFin :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Set
InjectiveFin {n} values =
  (i j : Fin n) ->
  values i == values j ->
  i == j

LastNonzeroFactorialDigitAt : Nat -> Nat -> Set
LastNonzeroFactorialDigitAt n digit =
  Exists Nat
    (\ trailingZeros ->
      Exists Nat
        (\ core ->
          (factorial n == core * power tenN trailingZeros)
          and
          Exists Nat
            (\ quotient ->
              (core == tenN * quotient + digit)
              and
              (Positive digit
               and
               (digit <N tenN)))))

LastNonzeroFactorialDigitFunction : (Nat -> Nat) -> Set
LastNonzeroFactorialDigitFunction f =
  (n : Nat) ->
  LastNonzeroFactorialDigitAt n (f n)

PeriodicFrom :
  Nat ->
  (Nat -> Nat) ->
  Nat ->
  Set
PeriodicFrom start g period =
  (s : Nat) ->
  start <=N s ->
  g s == g (s + period)

LeastPositivePeriodFrom :
  Nat ->
  (Nat -> Nat) ->
  Nat ->
  Set
LeastPositivePeriodFrom start g period =
  Positive period
  and
  (PeriodicFrom start g period
   and
   ((q : Nat) ->
     Positive q ->
     PeriodicFrom start g q ->
     period <=N q))

DependsOnlyOnExponentSum :
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Set
DependsOnlyOnExponentSum f g =
  (k : Nat) ->
  Positive k ->
  (a : Fin k -> Nat) ->
  InjectiveFin a ->
  f (sumFin (\ i -> power fiveN (a i)))
  ==
  g (sumFin a)

putnam-1984-a6 : Set
putnam-1984-a6 =
  (f : Nat -> Nat) ->
  LastNonzeroFactorialDigitFunction f ->
  Exists (Nat -> Nat)
    (\ g ->
      DependsOnlyOnExponentSum f g
      and
      LeastPositivePeriodFrom oneN g fourN)
