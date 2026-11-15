-- Statement-only formalization of thousand-theorems corpus artifact Q420714,
-- "Akra–Bazzi theorem": a real-valued divide-and-conquer recurrence satisfying
-- the Akra–Bazzi positivity, growth, and approximation hypotheses is big-O of
-- its canonical asymptotic bound. This file contains no proof.

{-# OPTIONS --safe #-}

module Q420714_akra_bazzi_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<N_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data _<N_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero <N suc n
  succ<succ : {m n : Nat} -> m <N n -> suc m <N suc n

data _<=N_ : Nat -> Nat -> Set where
  zero<=     : {n : Nat} -> zero <=N n
  succ<=succ : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR absoluteR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) -> addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) -> addR x zeroR == x
    add-inverseR :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) -> multiplyR x oneR == x
    multiply-zeroR :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexiveR :
      (x : R) -> lessOrEqualR x x
    order-transitiveR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-totalR :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-orderR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    absolute-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR (absoluteR x)
    absolute-of-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x
    absolute-of-nonpositiveR :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x
    absolute-zero-onlyR :
      (x : R) ->
      absoluteR x == zeroR ->
      x == zeroR
    absolute-addR :
      (x y : R) ->
      lessOrEqualR
        (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y))
    absolute-multiplyR :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-additionR :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNat-multiplicationR :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) ->
              P x ->
              lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) ->
                P x ->
                lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

divideR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divideR reals x y =
  multiplyR reals x (reciprocalR reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

Nonnegative :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Nonnegative reals x =
  lessOrEqualR reals (zeroR reals) x

powerNatR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
powerNatR reals x zero =
  oneR reals
powerNatR reals x (suc n) =
  multiplyR reals (powerNatR reals x n) x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

exponentialTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divideR reals
    (powerNatR reals x n)
    (fromNatR reals (factorial n))

exponentialPartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialPartialSum reals x zero =
  zeroR reals
exponentialPartialSum reals x (suc n) =
  addR reals
    (exponentialPartialSum reals x n)
    (exponentialTerm reals x n)

RealSequenceLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
RealSequenceLimit {R = R} reals sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      lessOrEqualR reals
        (absoluteR reals
          (subtractR reals (sequence n) limit))
        epsilon)

ExponentialValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
ExponentialValue reals exponent value =
  RealSequenceLimit reals
    (exponentialPartialSum reals exponent)
    value

record StandardRealAnalysis (R : Set) : Set1 where
  field
    algebra :
      CompleteOrderedField R
    logarithm :
      R -> R
    realPower :
      R -> R -> R

    logarithm-zero :
      logarithm (zeroR algebra) == zeroR algebra
    logarithm-positive :
      (x : R) ->
      Positive algebra x ->
      ExponentialValue algebra (logarithm x) x

    realPower-zero-zero :
      realPower (zeroR algebra) (zeroR algebra) == oneR algebra
    realPower-zero-nonzero :
      (q : R) ->
      q != zeroR algebra ->
      realPower (zeroR algebra) q == zeroR algebra
    realPower-positive :
      (x q : R) ->
      Positive algebra x ->
      ExponentialValue algebra
        (multiplyR algebra (logarithm x) q)
        (realPower x q)

open StandardRealAnalysis

sumFin :
  {R : Set} ->
  CompleteOrderedField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} terms =
  zeroR reals
sumFin reals {suc n} terms =
  addR reals
    (terms fzero)
    (sumFin reals (\ i -> terms (fsuc i)))

partialSumR :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
partialSumR reals terms zero =
  zeroR reals
partialSumR reals terms (suc n) =
  addR reals
    (partialSumR reals terms n)
    (terms n)

EventuallyNat :
  (Nat -> Set) ->
  Set
EventuallyNat property =
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      property n)

EventuallyReal :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> Set) ->
  Set
EventuallyReal {R = R} reals property =
  Exists R
    (\ cutoff ->
      (x : R) ->
      lessOrEqualR reals cutoff x ->
      property x)

IsLittleONat :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  (Nat -> R) ->
  Set
IsLittleONat {R = R} reals f h =
  (epsilon : R) ->
  Positive reals epsilon ->
  EventuallyNat
    (\ n ->
      lessOrEqualR reals
        (absoluteR reals (f n))
        (multiplyR reals epsilon (absoluteR reals (h n))))

IsBigONat :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  (Nat -> R) ->
  Set
IsBigONat {R = R} reals f h =
  Exists R
    (\ constant ->
      Both
        (Nonnegative reals constant)
        (EventuallyNat
          (\ n ->
            lessOrEqualR reals
              (absoluteR reals (f n))
              (multiplyR reals constant
                (absoluteR reals (h n))))))

GrowsPolynomially :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Set
GrowsPolynomially {R = R} reals g =
  (scale : R) ->
  Positive reals scale ->
  StrictLess reals scale (oneR reals) ->
  Exists R
    (\ lowerConstant ->
      Both
        (Positive reals lowerConstant)
        (Exists R
          (\ upperConstant ->
            Both
              (Positive reals upperConstant)
              (EventuallyReal reals
                (\ x ->
                  (u : R) ->
                  lessOrEqualR reals
                    (multiplyR reals scale x)
                    u ->
                  lessOrEqualR reals u x ->
                  Both
                    (lessOrEqualR reals
                      (multiplyR reals lowerConstant (g x))
                      (g u))
                    (lessOrEqualR reals
                      (g u)
                      (multiplyR reals upperConstant (g x))))))))

recurrenceSum :
  {R : Set} ->
  (analysis : StandardRealAnalysis R) ->
  {branchCount : Nat} ->
  (Fin (suc branchCount) -> R) ->
  (Nat -> R) ->
  (Fin (suc branchCount) -> Nat -> Nat) ->
  Nat ->
  R
recurrenceSum analysis coefficients cost subproblem n =
  sumFin (algebra analysis)
    (\ i ->
      multiplyR (algebra analysis)
        (coefficients i)
        (cost (subproblem i n)))

distanceScale :
  {R : Set} ->
  StandardRealAnalysis R ->
  Nat ->
  R
distanceScale analysis n =
  divideR reals
    (fromNatR reals n)
    (powerNatR reals
      (logarithm analysis (fromNatR reals n))
      (suc (suc zero)))
  where
    reals = algebra analysis

record AkraBazziRecurrence
  {R : Set}
  (analysis : StandardRealAnalysis R)
  {branchCount : Nat}
  (cost : Nat -> R)
  (toll : R -> R)
  (coefficient shrink : Fin (suc branchCount) -> R)
  (subproblem : Fin (suc branchCount) -> Nat -> Nat) :
  Set where

  private
    reals = algebra analysis

  field
    baseCutoff :
      Nat
    baseCutoff-positive :
      zero <N baseCutoff

    coefficient-positive :
      (i : Fin (suc branchCount)) ->
      Positive reals (coefficient i)
    shrink-positive :
      (i : Fin (suc branchCount)) ->
      Positive reals (shrink i)
    shrink-less-than-one :
      (i : Fin (suc branchCount)) ->
      StrictLess reals (shrink i) (oneR reals)

    toll-nonnegative :
      (x : R) ->
      Nonnegative reals x ->
      Nonnegative reals (toll x)
    toll-grows-polynomially :
      GrowsPolynomially reals toll

    recurrence :
      (n : Nat) ->
      baseCutoff <=N n ->
      cost n ==
      addR reals
        (recurrenceSum analysis coefficient cost subproblem n)
        (toll (fromNatR reals n))

    base-cost-positive :
      (n : Nat) ->
      n <N baseCutoff ->
      Positive reals (cost n)

    subproblem-smaller :
      (i : Fin (suc branchCount)) ->
      (n : Nat) ->
      baseCutoff <=N n ->
      subproblem i n <N n

    subproblem-approximates-shrink :
      (i : Fin (suc branchCount)) ->
      IsLittleONat reals
        (\ n ->
          subtractR reals
            (fromNatR reals (subproblem i n))
            (multiplyR reals
              (shrink i)
              (fromNatR reals n)))
        (distanceScale analysis)

coefficientPowerSum :
  {R : Set} ->
  (analysis : StandardRealAnalysis R) ->
  {branchCount : Nat} ->
  (Fin (suc branchCount) -> R) ->
  (Fin (suc branchCount) -> R) ->
  R ->
  R
coefficientPowerSum analysis coefficient shrink exponent =
  sumFin reals
    (\ i ->
      multiplyR reals
        (coefficient i)
        (realPower analysis (shrink i) exponent))
  where
    reals = algebra analysis

asymptoticBound :
  {R : Set} ->
  StandardRealAnalysis R ->
  (R -> R) ->
  R ->
  Nat ->
  R
asymptoticBound analysis toll exponent n =
  addR reals
    nPower
    (multiplyR reals nPower
      (partialSumR reals
        (\ u ->
          divideR reals
            (toll (fromNatR reals u))
            (realPower analysis
              (fromNatR reals u)
              (addR reals exponent (oneR reals))))
        n))
  where
    reals = algebra analysis
    nPower =
      realPower analysis (fromNatR reals n) exponent

record AkraBazziUpperBound
  {R : Set}
  (analysis : StandardRealAnalysis R)
  {branchCount : Nat}
  (cost : Nat -> R)
  (toll : R -> R)
  (coefficient shrink : Fin (suc branchCount) -> R) :
  Set where

  private
    reals = algebra analysis

  field
    exponent :
      R
    exponent-equation :
      coefficientPowerSum analysis coefficient shrink exponent ==
      oneR reals
    cost-is-big-o :
      IsBigONat reals cost
        (asymptoticBound analysis toll exponent)

akra-bazzi-theorem : Set1
akra-bazzi-theorem =
  (R : Set) ->
  (analysis : StandardRealAnalysis R) ->
  (branchCount : Nat) ->
  (cost : Nat -> R) ->
  (toll : R -> R) ->
  (coefficient shrink : Fin (suc branchCount) -> R) ->
  (subproblem : Fin (suc branchCount) -> Nat -> Nat) ->
  AkraBazziRecurrence
    analysis cost toll coefficient shrink subproblem ->
  AkraBazziUpperBound
    analysis cost toll coefficient shrink
