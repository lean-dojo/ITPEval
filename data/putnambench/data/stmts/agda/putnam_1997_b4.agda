-- Statement-only formalization of PutnamBench corpus artifact putnam_1997_b4:
-- coefficients of powers of 1 + x + x^2 satisfy an alternating-sum bound
-- between zero and one. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infix 4 _<=N_ _<=Z_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data _<=Z_ : Int -> Int -> Set where
  negative<=positive :
    {m n : Nat} ->
    negsuc m <=Z pos n
  positive<=positive :
    {m n : Nat} ->
    m <=N n ->
    pos m <=Z pos n
  negative<=negative :
    {m n : Nat} ->
    n <=N m ->
    negsuc m <=Z negsuc n

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

negativeNat : Nat -> Int
negativeNat zero =
  pos zero
negativeNat (suc n) =
  negsuc n

differenceNat : Nat -> Nat -> Int
differenceNat zero zero =
  pos zero
differenceNat (suc m) zero =
  pos (suc m)
differenceNat zero (suc n) =
  negsuc n
differenceNat (suc m) (suc n) =
  differenceNat m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  differenceNat m (suc n)
addInt (negsuc m) (pos n) =
  differenceNat n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negativeNat (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negativeNat (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

powerInt : Int -> Nat -> Int
powerInt x zero =
  pos oneN
powerInt x (suc n) =
  multiplyInt x (powerInt x n)

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

trinomialCoefficient : Nat -> Nat -> Nat
trinomialCoefficient zero zero =
  oneN
trinomialCoefficient zero (suc n) =
  zero
trinomialCoefficient (suc m) zero =
  trinomialCoefficient m zero
trinomialCoefficient (suc m) (suc zero) =
  trinomialCoefficient m (suc zero)
  + trinomialCoefficient m zero
trinomialCoefficient (suc m) (suc (suc n)) =
  trinomialCoefficient m (suc (suc n))
  + trinomialCoefficient m (suc n)
  + trinomialCoefficient m n

CoefficientSpecification :
  (Nat -> Nat -> Int) ->
  Set
CoefficientSpecification a =
  (m n : Nat) ->
  a m n == pos (trinomialCoefficient m n)

sumThroughInt :
  Nat ->
  (Nat -> Int) ->
  Int
sumThroughInt zero term =
  term zero
sumThroughInt (suc n) term =
  addInt
    (sumThroughInt n term)
    (term (suc n))

alternatingCoefficientSum :
  (Nat -> Nat -> Int) ->
  Nat ->
  Int
alternatingCoefficientSum a k =
  sumThroughInt
    (naturalDiv (twoN * k) threeN)
    (\ i ->
      multiplyInt
        (powerInt (negsuc zero) i)
        (a (k - i) i))

InZeroOne : Int -> Set
InZeroOne value =
  pos zero <=Z value
  and
  value <=Z pos oneN

putnam-1997-b4 : Set
putnam-1997-b4 =
  (a : Nat -> Nat -> Int) ->
  CoefficientSpecification a ->
  (k : Nat) ->
  InZeroOne (alternatingCoefficientSum a k)
