-- Statement-only formalization of thousand-theorems corpus artifact Q3527118,
-- "Mahler's theorem": the canonical Mahler series of a continuous function
-- on the p-adic integers converges uniformly to that function. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Q3527118_mahler_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _!=_ _<=N_ _<N_ _dividesN_ _dividesI_

data Bottom : Set where

record Top : Set where
  constructor top

Not : Set -> Set
Not A =
  A -> Bottom

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

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

record _dividesN_ (divisor dividend : Nat) : Set where
  field
    quotientN : Nat
    equationN : divisor * quotientN == dividend

record Prime (p : Nat) : Set where
  field
    at-least-two :
      suc (suc zero) <=N p
    only-trivial-divisors :
      (d : Nat) ->
      d dividesN p ->
      Either (d == suc zero) (d == p)

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  suc zero
naturalPower base (suc exponent) =
  base * naturalPower base exponent

natPred : Nat -> Nat
natPred zero =
  zero
natPred (suc n) =
  n

negativeNat : Nat -> Int
negativeNat zero =
  pos zero
negativeNat (suc n) =
  negsuc n

intNegate : Int -> Int
intNegate (pos n) =
  negativeNat n
intNegate (negsuc n) =
  pos (suc n)

intDifference : Nat -> Nat -> Int
intDifference zero zero =
  pos zero
intDifference (suc m) zero =
  pos (suc m)
intDifference zero (suc n) =
  negsuc n
intDifference (suc m) (suc n) =
  intDifference m n

intAdd : Int -> Int -> Int
intAdd (pos m) (pos n) =
  pos (m + n)
intAdd (pos m) (negsuc n) =
  intDifference m (suc n)
intAdd (negsuc m) (pos n) =
  intDifference n (suc m)
intAdd (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

intMultiply : Int -> Int -> Int
intMultiply (pos m) (pos n) =
  pos (m * n)
intMultiply (pos m) (negsuc n) =
  negativeNat (m * suc n)
intMultiply (negsuc m) (pos n) =
  negativeNat (suc m * n)
intMultiply (negsuc m) (negsuc n) =
  pos (suc m * suc n)

intSubtract : Int -> Int -> Int
intSubtract x y =
  intAdd x (intNegate y)

record _dividesI_ (divisor dividend : Int) : Set where
  field
    quotientI : Int
    equationI : intMultiply divisor quotientI == dividend

-- Positive rationals use positive numerator and denominator codes.  Their
-- cross-multiplication relations quotient this concrete representation.
record PositiveRational : Set where
  constructor positive-rational
  field
    numeratorCode   : Nat
    denominatorCode : Nat

open PositiveRational

numeratorValue : PositiveRational -> Nat
numeratorValue q =
  suc (numeratorCode q)

denominatorValue : PositiveRational -> Nat
denominatorValue q =
  suc (denominatorCode q)

RationalEqual : PositiveRational -> PositiveRational -> Set
RationalEqual q r =
  numeratorValue q * denominatorValue r ==
  numeratorValue r * denominatorValue q

RationalLT : PositiveRational -> PositiveRational -> Set
RationalLT q r =
  numeratorValue q * denominatorValue r
    <N
  numeratorValue r * denominatorValue q

divideByPadicPower :
  PositiveRational ->
  Nat ->
  Nat ->
  PositiveRational
divideByPadicPower q p k =
  positive-rational
    (numeratorCode q)
    (natPred (denominatorValue q * naturalPower p k))

-- This is a fixed extensional construction of the nonnegative real line:
-- finite located upper Dedekind cuts of the positive rationals.
record Magnitude : Set1 where
  field
    upper :
      PositiveRational ->
      Set

    upper-respects-rational-equality :
      (q r : PositiveRational) ->
      RationalEqual q r ->
      Iff (upper q) (upper r)

    upper-inhabited :
      Exists PositiveRational upper

    upper-upward :
      (q r : PositiveRational) ->
      RationalLT q r ->
      upper q ->
      upper r

    upper-rounded :
      (q : PositiveRational) ->
      upper q ->
      Exists PositiveRational
        (\ r -> Both (RationalLT r q) (upper r))

    upper-located :
      (q r : PositiveRational) ->
      RationalLT q r ->
      Either (upper r) (Not (upper q))

open Magnitude

MagnitudeEqual : Magnitude -> Magnitude -> Set
MagnitudeEqual x y =
  (q : PositiveRational) ->
  Iff (upper x q) (upper y q)

-- A p-adic integer is represented by a formal sum sum_i a_i p^i with
-- integer coefficients.  PadicEqual below is the extensional quotient
-- relation identifying series congruent modulo every p^k.
PadicInteger : Nat -> Set
PadicInteger p =
  Nat -> Int

padicZero : (p : Nat) -> PadicInteger p
padicZero p n =
  pos zero

padicOne : (p : Nat) -> PadicInteger p
padicOne p zero =
  pos (suc zero)
padicOne p (suc n) =
  pos zero

padicFromNat : (p : Nat) -> Nat -> PadicInteger p
padicFromNat p n zero =
  pos n
padicFromNat p n (suc k) =
  pos zero

padicAdd :
  (p : Nat) ->
  PadicInteger p ->
  PadicInteger p ->
  PadicInteger p
padicAdd p x y n =
  intAdd (x n) (y n)

padicNegate :
  (p : Nat) ->
  PadicInteger p ->
  PadicInteger p
padicNegate p x n =
  intNegate (x n)

convolutionAux :
  (p : Nat) ->
  PadicInteger p ->
  PadicInteger p ->
  Nat ->
  Nat ->
  Nat ->
  Int
convolutionAux p x y i j zero =
  intMultiply (x i) (y j)
convolutionAux p x y i j (suc count) =
  intAdd
    (intMultiply (x i) (y j))
    (convolutionAux p x y (suc i) (natPred j) count)

padicMultiply :
  (p : Nat) ->
  PadicInteger p ->
  PadicInteger p ->
  PadicInteger p
padicMultiply p x y n =
  convolutionAux p x y zero n n

padicPrefix :
  (p : Nat) ->
  PadicInteger p ->
  Nat ->
  Int
padicPrefix p x zero =
  pos zero
padicPrefix p x (suc k) =
  intAdd
    (padicPrefix p x k)
    (intMultiply (x k) (pos (naturalPower p k)))

PadicCongruent :
  (p : Nat) ->
  Nat ->
  PadicInteger p ->
  PadicInteger p ->
  Set
PadicCongruent p k x y =
  pos (naturalPower p k)
    dividesI
  intSubtract (padicPrefix p x k) (padicPrefix p y k)

PadicEqual :
  (p : Nat) ->
  PadicInteger p ->
  PadicInteger p ->
  Set
PadicEqual p x y =
  (k : Nat) ->
  PadicCongruent p k x y

PadicContinuous :
  (p : Nat) ->
  (PadicInteger p -> PadicInteger p) ->
  Set
PadicContinuous p function =
  (x : PadicInteger p) ->
  (outputPrecision : Nat) ->
  Exists Nat
    (\ inputPrecision ->
      (y : PadicInteger p) ->
      PadicCongruent p inputPrecision y x ->
      PadicCongruent p outputPrecision
        (function y)
        (function x))

choose : Nat -> Nat -> Nat
choose zero zero =
  suc zero
choose zero (suc k) =
  zero
choose (suc n) zero =
  suc zero
choose (suc n) (suc k) =
  choose n k + choose n (suc k)

MahlerExtension :
  (p : Nat) ->
  (Nat -> PadicInteger p -> PadicInteger p) ->
  Set
MahlerExtension p basis =
  Both
    ((k : Nat) ->
      (x y : PadicInteger p) ->
      PadicEqual p x y ->
      PadicEqual p (basis k x) (basis k y))
    (Both
      ((k : Nat) ->
        PadicContinuous p (basis k))
      ((k n : Nat) ->
        PadicEqual p
          (basis k (padicFromNat p n))
          (padicFromNat p (choose n k))))

-- The canonical basis is characterized internally, rather than supplied as
-- a theorem parameter: it is the unique continuous extension of binomial
-- coefficients from the dense natural numbers.
record CanonicalMahler
  (p : Nat)
  (basis : Nat -> PadicInteger p -> PadicInteger p) :
  Set where

  field
    extension-properties :
      MahlerExtension p basis

    unique-extension :
      (other : Nat -> PadicInteger p -> PadicInteger p) ->
      MahlerExtension p other ->
      (k : Nat) ->
      (x : PadicInteger p) ->
      PadicEqual p (other k x) (basis k x)

record PAdicBanachModule (p : Nat) (E : Set) : Set1 where
  field
    zeroE :
      E
    addE :
      E -> E -> E
    negateE :
      E -> E
    scaleE :
      PadicInteger p -> E -> E
    normE :
      E -> Magnitude

    add-commutativeE :
      (x y : E) -> addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) -> addE x zeroE == x
    add-inverseE :
      (x : E) -> addE x (negateE x) == zeroE

    scale-respects-padicsE :
      (a b : PadicInteger p) ->
      PadicEqual p a b ->
      (x : E) ->
      scaleE a x == scaleE b x
    scale-oneE :
      (x : E) ->
      scaleE (padicOne p) x == x
    scale-associativeE :
      (a b : PadicInteger p) ->
      (x : E) ->
      scaleE (padicMultiply p a b) x ==
      scaleE a (scaleE b x)
    scale-add-scalarsE :
      (a b : PadicInteger p) ->
      (x : E) ->
      scaleE (padicAdd p a b) x ==
      addE (scaleE a x) (scaleE b x)
    scale-add-vectorsE :
      (a : PadicInteger p) ->
      (x y : E) ->
      scaleE a (addE x y) ==
      addE (scaleE a x) (scaleE a y)
    scale-zero-scalarE :
      (x : E) ->
      scaleE (padicZero p) x == zeroE
    scale-zero-vectorE :
      (a : PadicInteger p) ->
      scaleE a zeroE == zeroE

    norm-zero-exactlyE :
      (x : E) ->
      Iff
        ((q : PositiveRational) -> upper (normE x) q)
        (x == zeroE)
    norm-negateE :
      (x : E) ->
      MagnitudeEqual (normE (negateE x)) (normE x)
    norm-ultrametricE :
      (x y : E) ->
      (q : PositiveRational) ->
      upper (normE x) q ->
      upper (normE y) q ->
      upper (normE (addE x y)) q

    -- PadicCongruent p k a 0 says |a|_p <= p^(-k), so this is exactly
    -- the bounded scalar-action inequality in rational upper-cut form.
    norm-scale-boundedE :
      (a : PadicInteger p) ->
      (x : E) ->
      (k : Nat) ->
      (q : PositiveRational) ->
      PadicCongruent p k a (padicZero p) ->
      upper (normE x) q ->
      upper (normE (scaleE a x))
        (divideByPadicPower q p k)

    completeE :
      (sequence : Nat -> E) ->
      ((epsilon : PositiveRational) ->
        Exists Nat
          (\ cutoff ->
            (m n : Nat) ->
            cutoff <=N m ->
            cutoff <=N n ->
            upper
              (normE
                (addE (sequence m) (negateE (sequence n))))
              epsilon)) ->
      Exists E
        (\ limit ->
          (epsilon : PositiveRational) ->
          Exists Nat
            (\ cutoff ->
              (n : Nat) ->
              cutoff <=N n ->
              upper
                (normE
                  (addE (sequence n) (negateE limit)))
                epsilon))

open PAdicBanachModule

subtractE :
  {p : Nat} ->
  {E : Set} ->
  PAdicBanachModule p E ->
  E ->
  E ->
  E
subtractE space x y =
  addE space x (negateE space y)

record ContinuousPadicMap
  {p : Nat}
  {E : Set}
  (space : PAdicBanachModule p E)
  (function : PadicInteger p -> E) :
  Set where

  field
    respects-padic-equality :
      (x y : PadicInteger p) ->
      PadicEqual p x y ->
      function x == function y

    continuous :
      (x : PadicInteger p) ->
      (epsilon : PositiveRational) ->
      Exists Nat
        (\ precision ->
          (y : PadicInteger p) ->
          PadicCongruent p precision y x ->
          upper
            (normE space
              (subtractE space (function y) (function x)))
            epsilon)

forwardDifference :
  {p : Nat} ->
  {E : Set} ->
  PAdicBanachModule p E ->
  Nat ->
  (PadicInteger p -> E) ->
  PadicInteger p ->
  E
forwardDifference space zero f x =
  f x
forwardDifference {p = p} space (suc n) f x =
  subtractE space
    (forwardDifference space n f
      (padicAdd p x (padicOne p)))
    (forwardDifference space n f x)

data Member {A : Set} (x : A) : List A -> Set where
  here  : {xs : List A} -> Member x (x ∷ xs)
  there : {y : A} {xs : List A} -> Member x xs -> Member x (y ∷ xs)

NoDuplicates : {A : Set} -> List A -> Set
NoDuplicates [] =
  Top
NoDuplicates (x ∷ xs) =
  Both (Not (Member x xs)) (NoDuplicates xs)

SubsetList : {A : Set} -> List A -> List A -> Set
SubsetList [] ys =
  Top
SubsetList (x ∷ xs) ys =
  Both (Member x ys) (SubsetList xs ys)

sumFunctions :
  {E X : Set} ->
  E ->
  (E -> E -> E) ->
  (Nat -> X -> E) ->
  List Nat ->
  X ->
  E
sumFunctions zeroValue addValue term [] x =
  zeroValue
sumFunctions zeroValue addValue term (n ∷ ns) x =
  addValue
    (term n x)
    (sumFunctions zeroValue addValue term ns x)

UniformHasSum :
  {E X : Set} ->
  E ->
  (E -> E -> E) ->
  (E -> E -> E) ->
  (E -> Magnitude) ->
  (Nat -> X -> E) ->
  (X -> E) ->
  Set
UniformHasSum zeroValue addValue subtractValue normValue term total =
  (epsilon : PositiveRational) ->
  Exists (List Nat)
    (\ base ->
      Both
        (NoDuplicates base)
        ((indices : List Nat) ->
          NoDuplicates indices ->
          SubsetList base indices ->
          (x : _) ->
          upper
            (normValue
              (subtractValue
                (sumFunctions
                  zeroValue addValue term indices x)
                (total x)))
            epsilon))

MahlerExpansion :
  {p : Nat} ->
  {E : Set} ->
  PAdicBanachModule p E ->
  (PadicInteger p -> E) ->
  Set
MahlerExpansion {p = p} space f =
  Exists
    (Nat -> PadicInteger p -> PadicInteger p)
    (\ mahler ->
      Both
        (CanonicalMahler p mahler)
        (UniformHasSum
          (zeroE space)
          (addE space)
          (subtractE space)
          (normE space)
          (\ n x ->
            scaleE space
              (mahler n x)
              (forwardDifference space n f (padicZero p)))
          f))

mahler-s-theorem : Set1
mahler-s-theorem =
  (p : Nat) ->
  Prime p ->
  (E : Set) ->
  (space : PAdicBanachModule p E) ->
  (f : PadicInteger p -> E) ->
  ContinuousPadicMap space f ->
  MahlerExpansion space f
