-- Statement-only formalization of PutnamBench corpus artifact putnam_2011_a6
-- (putnambench__agda__putnam_2011_a6): exponential-rate convergence to the
-- uniform distribution for a generating die on a finite abelian group.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2011A6 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
infixr 5 _::_

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

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data _<N_ : Nat -> Nat -> Set where
  zero<sucN : {n : Nat} -> zero <N suc n
  suc<sucN  : {m n : Nat} -> m <N n -> suc m <N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

sameFin : {n : Nat} -> Fin n -> Fin n -> Bool
sameFin fzero fzero =
  true
sameFin fzero (fsuc j) =
  false
sameFin (fsuc i) fzero =
  false
sameFin (fsuc i) (fsuc j) =
  sameFin i j

ifBool : {A : Set} -> Bool -> A -> A -> A
ifBool true whenTrue whenFalse =
  whenTrue
ifBool false whenTrue whenFalse =
  whenFalse

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

naturalPowerNat : Nat -> Nat -> Nat
naturalPowerNat base zero =
  oneN
naturalPowerNat base (suc exponent) =
  base * naturalPowerNat base exponent

sumNatFin :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
sumNatFin {zero} term =
  zero
sumNatFin {suc n} term =
  term fzero +
  sumNatFin (\ i -> term (fsuc i))

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc exponent) =
  multiply reals
    (naturalPower reals x exponent)
    x

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (m : Nat) ->
      cutoff <=N m ->
      CloseTo reals limit epsilon (sequence m))

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} term =
  zeroR reals
sumFin reals {suc n} term =
  add reals
    (term fzero)
    (sumFin reals (\ i -> term (fsuc i)))

record FiniteCommutativeGroup (n : Nat) : Set1 where
  field
    Carrier :
      Set
    identity :
      Carrier
    multiplyG :
      Carrier ->
      Carrier ->
      Carrier
    inverseG :
      Carrier ->
      Carrier

    associative :
      (x y z : Carrier) ->
      multiplyG (multiplyG x y) z ==
      multiplyG x (multiplyG y z)
    identity-left :
      (x : Carrier) ->
      multiplyG identity x == x
    identity-right :
      (x : Carrier) ->
      multiplyG x identity == x
    inverse-left :
      (x : Carrier) ->
      multiplyG (inverseG x) x == identity
    inverse-right :
      (x : Carrier) ->
      multiplyG x (inverseG x) == identity
    commutative :
      (x y : Carrier) ->
      multiplyG x y == multiplyG y x

    toFin :
      Carrier ->
      Fin n
    fromFin :
      Fin n ->
      Carrier
    from-to :
      (x : Carrier) ->
      fromFin (toFin x) == x
    to-from :
      (i : Fin n) ->
      toFin (fromFin i) == i

open FiniteCommutativeGroup

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective {A = A} f =
  (x y : A) ->
  f x == f y ->
  x == y

productWord :
  {n k m : Nat} ->
  (G : FiniteCommutativeGroup n) ->
  (generators : Fin k -> Carrier G) ->
  Vec (Fin k) m ->
  Carrier G
productWord G generators [] =
  identity G
productWord G generators (i :: word) =
  multiplyG G
    (generators i)
    (productWord G generators word)

IdentityIncluded :
  {n k : Nat} ->
  (G : FiniteCommutativeGroup n) ->
  (Fin k -> Carrier G) ->
  Set
IdentityIncluded G generators =
  Exists (Fin _)
    (\ i ->
      generators i == identity G)

Generates :
  {n k : Nat} ->
  (G : FiniteCommutativeGroup n) ->
  (Fin k -> Carrier G) ->
  Set
Generates G generators =
  (x : Carrier G) ->
  Exists Nat
    (\ m ->
      Exists (Vec (Fin _) m)
        (\ word ->
          productWord G generators word == x))

wordCount :
  {n k : Nat} ->
  (G : FiniteCommutativeGroup n) ->
  (generators : Fin k -> Carrier G) ->
  Nat ->
  Carrier G ->
  Nat
wordCount G generators zero x =
  ifBool
    (sameFin (toFin G x) (toFin G (identity G)))
    oneN
    zero
wordCount G generators (suc m) x =
  sumNatFin
    (\ i ->
      wordCount G generators m
        (multiplyG G
          (inverseG G (generators i))
          x))

dieProbability :
  {R : Set} {n k : Nat} ->
  CompleteOrderedRealField R ->
  (G : FiniteCommutativeGroup n) ->
  (Fin k -> Carrier G) ->
  Nat ->
  Carrier G ->
  R
dieProbability {k = k} reals G generators m x =
  divide reals
    (fromNat reals (wordCount G generators m x))
    (fromNat reals (naturalPowerNat k m))

squaredDistanceFromUniform :
  {R : Set} {n k : Nat} ->
  CompleteOrderedRealField R ->
  (G : FiniteCommutativeGroup n) ->
  (Fin k -> Carrier G) ->
  Nat ->
  R
squaredDistanceFromUniform {n = n} reals G generators m =
  sumFin reals
    (\ i ->
      square reals
        (subtract reals
          (dieProbability reals G generators m (fromFin G i))
          (divide reals
            (oneR reals)
            (fromNat reals n))))

normalizedSquaredDistance :
  {R : Set} {n k : Nat} ->
  CompleteOrderedRealField R ->
  (G : FiniteCommutativeGroup n) ->
  (Fin k -> Carrier G) ->
  R ->
  Nat ->
  R
normalizedSquaredDistance reals G generators b m =
  multiply reals
    (divide reals
      (oneR reals)
      (naturalPower reals b (twoN * m)))
    (squaredDistanceFromUniform reals G generators m)

PutnamConclusion :
  {R : Set} {n k : Nat} ->
  CompleteOrderedRealField R ->
  (G : FiniteCommutativeGroup n) ->
  (Fin k -> Carrier G) ->
  Set
PutnamConclusion {R} reals G generators =
  Exists R
    (\ b ->
      (StrictLess reals (zeroR reals) b
      and
      StrictLess reals b (oneR reals))
      and
      Exists R
        (\ C ->
          StrictLess reals (zeroR reals) C
          and
          ConvergesTo reals
            (normalizedSquaredDistance reals G generators b)
            C))

putnam-2011-a6 : Set1
putnam-2011-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n k : Nat) ->
  (G : FiniteCommutativeGroup n) ->
  (generators : Fin k -> Carrier G) ->
  Injective generators ->
  k <N n ->
  IdentityIncluded G generators ->
  Generates G generators ->
  PutnamConclusion reals G generators
