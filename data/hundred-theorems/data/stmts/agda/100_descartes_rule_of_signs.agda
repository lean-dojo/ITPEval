-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__100, "Descartes Rule of Signs": positive roots
-- counted with multiplicity are bounded by coefficient sign variations, and
-- for nonzero real polynomials the difference is even. This file contains no proof.

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _!=_ _↔_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record _↔_ (A B : Set) : Set where
  field
    forward  : A -> B
    backward : B -> A

ExcludedMiddle : Set1
ExcludedMiddle =
  (P : Set) -> Either P (Not P)

data Sign : Set where
  negative zeroSign positive : Sign

record CompleteArchimedeanOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R
    signR : R -> Sign

    oneR-not-zeroR :
      oneR != zeroR

    addR-commutative :
      (x y : R) -> addR x y == addR y x
    addR-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    addR-zero :
      (x : R) -> addR x zeroR == x
    addR-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiplyR-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiplyR-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiplyR-one :
      (x : R) -> multiplyR x oneR == x
    multiplyR-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    multiplyR-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    addR-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiplyR-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zeroR-less-than-oneR :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    fromNatR-zero :
      fromNatR zero == zeroR
    fromNatR-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNatR-injective :
      (m n : Nat) -> fromNatR m == fromNatR n -> m == n

    archimedean :
      (x : R) ->
      Σ Nat (\ n -> lessOrEqualR x (fromNatR n))

    least-upper-bound :
      (P : R -> Set) ->
      Σ R (\ x -> P x) ->
      Σ R (\ upper -> (x : R) -> P x -> lessOrEqualR x upper) ->
      Σ R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

    sign-negative :
      (x : R) ->
      (signR x == negative) ↔
      Both (lessOrEqualR x zeroR) (x != zeroR)
    sign-zero :
      (x : R) ->
      (signR x == zeroSign) ↔ (x == zeroR)
    sign-positive :
      (x : R) ->
      (signR x == positive) ↔
      Both (lessOrEqualR zeroR x) (x != zeroR)

open CompleteArchimedeanOrderedField

Positive :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  R ->
  Set
Positive reals x =
  Both (lessOrEqualR reals (zeroR reals) x) (x != zeroR reals)

mapSign :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  List R ->
  List Sign
mapSign reals [] = []
mapSign reals (x ∷ xs) = signR reals x ∷ mapSign reals xs

mutual
  changesFrom : Sign -> List Sign -> Nat
  changesFrom previous [] = zero
  changesFrom previous (zeroSign ∷ signs) =
    changesFrom previous signs
  changesFrom negative (negative ∷ signs) =
    changesFrom negative signs
  changesFrom negative (positive ∷ signs) =
    suc (changesFrom positive signs)
  changesFrom positive (negative ∷ signs) =
    suc (changesFrom negative signs)
  changesFrom positive (positive ∷ signs) =
    changesFrom positive signs
  changesFrom zeroSign signs =
    signVariationsSigns signs

  signVariationsSigns : List Sign -> Nat
  signVariationsSigns [] = zero
  signVariationsSigns (zeroSign ∷ signs) =
    signVariationsSigns signs
  signVariationsSigns (negative ∷ signs) =
    changesFrom negative signs
  signVariationsSigns (positive ∷ signs) =
    changesFrom positive signs

signVariations :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  List R ->
  Nat
signVariations reals coefficients =
  signVariationsSigns (mapSign reals coefficients)

length : {A : Set} -> List A -> Nat
length [] = zero
length (x ∷ xs) = suc (length xs)

Even : Nat -> Set
Even n =
  Σ Nat (\ k -> n == k + k)

module PolynomialDefinitions
  {R : Set}
  (reals : CompleteArchimedeanOrderedField R) where

  Polynomial : Set
  Polynomial = List R

  coefficient : Polynomial -> Nat -> R
  coefficient [] n = zeroR reals
  coefficient (c ∷ coefficients) zero = c
  coefficient (c ∷ coefficients) (suc n) =
    coefficient coefficients n

  infix 4 _≈P_

  _≈P_ : Polynomial -> Polynomial -> Set
  p ≈P q =
    (n : Nat) -> coefficient p n == coefficient q n

  addPolynomial : Polynomial -> Polynomial -> Polynomial
  addPolynomial [] q = q
  addPolynomial p [] = p
  addPolynomial (a ∷ p) (b ∷ q) =
    addR reals a b ∷ addPolynomial p q

  scalePolynomial : R -> Polynomial -> Polynomial
  scalePolynomial c [] = []
  scalePolynomial c (a ∷ p) =
    multiplyR reals c a ∷ scalePolynomial c p

  multiplyPolynomial : Polynomial -> Polynomial -> Polynomial
  multiplyPolynomial [] q = []
  multiplyPolynomial (a ∷ p) q =
    addPolynomial
      (scalePolynomial a q)
      (zeroR reals ∷ multiplyPolynomial p q)

  onePolynomial : Polynomial
  onePolynomial = oneR reals ∷ []

  linearFactor : R -> Polynomial
  linearFactor r =
    negateR reals r ∷ oneR reals ∷ []

  powerPolynomial : Polynomial -> Nat -> Polynomial
  powerPolynomial p zero = onePolynomial
  powerPolynomial p (suc n) =
    multiplyPolynomial (powerPolynomial p n) p

  evaluate : Polynomial -> R -> R
  evaluate [] x = zeroR reals
  evaluate (a ∷ p) x =
    addR reals a (multiplyR reals x (evaluate p x))

  NonzeroPolynomial : Polynomial -> Set
  NonzeroPolynomial p =
    Σ Nat (\ n -> coefficient p n != zeroR reals)

  data Occurrences (r : R) : List R -> Nat -> Set where
    occurrences-empty :
      Occurrences r [] zero
    occurrences-equal :
      {x : R} {xs : List R} {k : Nat} ->
      r == x ->
      Occurrences r xs k ->
      Occurrences r (x ∷ xs) (suc k)
    occurrences-different :
      {x : R} {xs : List R} {k : Nat} ->
      r != x ->
      Occurrences r xs k ->
      Occurrences r (x ∷ xs) k

  data AllPositive : List R -> Set where
    all-positive-empty :
      AllPositive []
    all-positive-cons :
      {r : R} {roots : List R} ->
      Positive reals r ->
      AllPositive roots ->
      AllPositive (r ∷ roots)

  MultiplicityAt : Polynomial -> R -> Nat -> Set
  MultiplicityAt p r k =
    Σ Polynomial
      (\ q ->
        Both
          (p ≈P
            multiplyPolynomial
              (powerPolynomial (linearFactor r) k)
              q)
          (evaluate q r != zeroR reals))

  PositiveRootEnumeration : Polynomial -> List R -> Set
  PositiveRootEnumeration p roots =
    Both
      (AllPositive roots)
      ((r : R) ->
        Positive reals r ->
        Σ Nat
          (\ k ->
            Both
              (Occurrences r roots k)
              (MultiplicityAt p r k)))

record StrictOrderedCommutativeRing (R : Set) : Set1 where
  field
    zeroG oneG : R
    addG multiplyG : R -> R -> R
    negateG : R -> R
    lessOrEqualG : R -> R -> Set
    signG : R -> Sign

    oneG-not-zeroG :
      oneG != zeroG

    addG-commutative :
      (x y : R) -> addG x y == addG y x
    addG-associative :
      (x y z : R) -> addG (addG x y) z == addG x (addG y z)
    addG-zero :
      (x : R) -> addG x zeroG == x
    addG-inverse :
      (x : R) -> addG x (negateG x) == zeroG

    multiplyG-commutative :
      (x y : R) -> multiplyG x y == multiplyG y x
    multiplyG-associative :
      (x y z : R) ->
      multiplyG (multiplyG x y) z == multiplyG x (multiplyG y z)
    multiplyG-one :
      (x : R) -> multiplyG x oneG == x
    multiplyG-zero :
      (x : R) -> multiplyG x zeroG == zeroG
    distributeG :
      (x y z : R) ->
      multiplyG x (addG y z) ==
      addG (multiplyG x y) (multiplyG x z)

    orderG-reflexive :
      (x : R) -> lessOrEqualG x x
    orderG-transitive :
      (x y z : R) ->
      lessOrEqualG x y ->
      lessOrEqualG y z ->
      lessOrEqualG x z
    orderG-antisymmetric :
      (x y : R) ->
      lessOrEqualG x y ->
      lessOrEqualG y x ->
      x == y
    orderG-total :
      (x y : R) ->
      Either (lessOrEqualG x y) (lessOrEqualG y x)
    addG-order :
      (x y z : R) ->
      lessOrEqualG x y ->
      lessOrEqualG (addG z x) (addG z y)
    multiplyG-nonnegative :
      (x y : R) ->
      lessOrEqualG zeroG x ->
      lessOrEqualG zeroG y ->
      lessOrEqualG zeroG (multiplyG x y)
    zeroG-less-than-oneG :
      Both (lessOrEqualG zeroG oneG) (zeroG != oneG)

    signG-negative :
      (x : R) ->
      (signG x == negative) ↔
      Both (lessOrEqualG x zeroG) (x != zeroG)
    signG-zero :
      (x : R) ->
      (signG x == zeroSign) ↔ (x == zeroG)
    signG-positive :
      (x : R) ->
      (signG x == positive) ↔
      Both (lessOrEqualG zeroG x) (x != zeroG)

open StrictOrderedCommutativeRing

PositiveG :
  {R : Set} ->
  StrictOrderedCommutativeRing R ->
  R ->
  Set
PositiveG ring x =
  Both (lessOrEqualG ring (zeroG ring) x) (x != zeroG ring)

mapSignG :
  {R : Set} ->
  StrictOrderedCommutativeRing R ->
  List R ->
  List Sign
mapSignG ring [] = []
mapSignG ring (x ∷ xs) = signG ring x ∷ mapSignG ring xs

signVariationsG :
  {R : Set} ->
  StrictOrderedCommutativeRing R ->
  List R ->
  Nat
signVariationsG ring coefficients =
  signVariationsSigns (mapSignG ring coefficients)

data NatLessOrEqual : Nat -> Nat -> Set where
  zero-less-or-equal :
    {n : Nat} ->
    NatLessOrEqual zero n
  successor-less-or-equal :
    {m n : Nat} ->
    NatLessOrEqual m n ->
    NatLessOrEqual (suc m) (suc n)

module OrderedPolynomialDefinitions
  {R : Set}
  (ring : StrictOrderedCommutativeRing R) where

  Polynomial : Set
  Polynomial = List R

  coefficient : Polynomial -> Nat -> R
  coefficient [] n = zeroG ring
  coefficient (c ∷ coefficients) zero = c
  coefficient (c ∷ coefficients) (suc n) =
    coefficient coefficients n

  infix 4 _≈G_

  _≈G_ : Polynomial -> Polynomial -> Set
  p ≈G q =
    (n : Nat) -> coefficient p n == coefficient q n

  addPolynomial : Polynomial -> Polynomial -> Polynomial
  addPolynomial [] q = q
  addPolynomial p [] = p
  addPolynomial (a ∷ p) (b ∷ q) =
    addG ring a b ∷ addPolynomial p q

  scalePolynomial : R -> Polynomial -> Polynomial
  scalePolynomial c [] = []
  scalePolynomial c (a ∷ p) =
    multiplyG ring c a ∷ scalePolynomial c p

  multiplyPolynomial : Polynomial -> Polynomial -> Polynomial
  multiplyPolynomial [] q = []
  multiplyPolynomial (a ∷ p) q =
    addPolynomial
      (scalePolynomial a q)
      (zeroG ring ∷ multiplyPolynomial p q)

  onePolynomial : Polynomial
  onePolynomial = oneG ring ∷ []

  linearFactor : R -> Polynomial
  linearFactor r =
    negateG ring r ∷ oneG ring ∷ []

  powerPolynomial : Polynomial -> Nat -> Polynomial
  powerPolynomial p zero = onePolynomial
  powerPolynomial p (suc n) =
    multiplyPolynomial (powerPolynomial p n) p

  evaluate : Polynomial -> R -> R
  evaluate [] x = zeroG ring
  evaluate (a ∷ p) x =
    addG ring a (multiplyG ring x (evaluate p x))

  ZeroPolynomial : Polynomial -> Set
  ZeroPolynomial p =
    (n : Nat) -> coefficient p n == zeroG ring

  NonzeroPolynomial : Polynomial -> Set
  NonzeroPolynomial p =
    Σ Nat (\ n -> coefficient p n != zeroG ring)

  data Occurrences (r : R) : List R -> Nat -> Set where
    occurrences-empty :
      Occurrences r [] zero
    occurrences-equal :
      {x : R} {xs : List R} {k : Nat} ->
      r == x ->
      Occurrences r xs k ->
      Occurrences r (x ∷ xs) (suc k)
    occurrences-different :
      {x : R} {xs : List R} {k : Nat} ->
      r != x ->
      Occurrences r xs k ->
      Occurrences r (x ∷ xs) k

  data AllPositive : List R -> Set where
    all-positive-empty :
      AllPositive []
    all-positive-cons :
      {r : R} {roots : List R} ->
      PositiveG ring r ->
      AllPositive roots ->
      AllPositive (r ∷ roots)

  MultiplicityAt : Polynomial -> R -> Nat -> Set
  MultiplicityAt p r k =
    Σ Polynomial
      (\ q ->
        Both
          (p ≈G
            multiplyPolynomial
              (powerPolynomial (linearFactor r) k)
              q)
          (evaluate q r != zeroG ring))

  PositiveRootEnumeration : Polynomial -> List R -> Set
  PositiveRootEnumeration p roots =
    Both
      (AllPositive roots)
      ((r : R) ->
        PositiveG ring r ->
        Σ Nat
          (\ k ->
            Both
              (Occurrences r roots k)
              (MultiplicityAt p r k)))

  data RootEnumeration (p : Polynomial) : List R -> Set where
    zero-root-enumeration :
      ZeroPolynomial p ->
      RootEnumeration p []
    nonzero-root-enumeration :
      {roots : List R} ->
      NonzeroPolynomial p ->
      PositiveRootEnumeration p roots ->
      RootEnumeration p roots

generic-descartes-bound : Set1
generic-descartes-bound =
  ExcludedMiddle ->
  (R : Set) ->
  (ring : StrictOrderedCommutativeRing R) ->
  (p : OrderedPolynomialDefinitions.Polynomial ring) ->
  Σ (List R)
    (\ positiveRoots ->
      Both
        (OrderedPolynomialDefinitions.RootEnumeration
          ring p positiveRoots)
        (NatLessOrEqual
          (length positiveRoots)
          (signVariationsG ring p)))

real-descartes-parity : Set1
real-descartes-parity =
  ExcludedMiddle ->
  (R : Set) ->
  (reals : CompleteArchimedeanOrderedField R) ->
  (p : PolynomialDefinitions.Polynomial reals) ->
  PolynomialDefinitions.NonzeroPolynomial reals p ->
  Σ (List R)
    (\ positiveRoots ->
      Both
        (PolynomialDefinitions.PositiveRootEnumeration
          reals p positiveRoots)
        (Σ Nat
          (\ d ->
            Both
              (Even d)
              (signVariations reals p ==
                length positiveRoots + d))))

record DescartesRuleOfSignsStatements : Set1 where
  field
    ordered-ring-bound :
      generic-descartes-bound
    real-even-difference :
      real-descartes-parity

descartes-rule-of-signs : Set1
descartes-rule-of-signs =
  DescartesRuleOfSignsStatements
