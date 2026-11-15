-- Statement-only formalization of PutnamBench corpus artifact putnam_1985_b1:
-- the distinct integers -2, -1, 0, 1, 2 minimize the number of nonzero
-- coefficients in a monic polynomial having five distinct integer roots.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin5 : Set where
  i0 i1 i2 i3 i4 : Fin5

Injective : {A B : Set} -> (A -> B) -> Set
Injective f =
  (x y : _) ->
  f x == f y ->
  x == y

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

negateInt : Int -> Int
negateInt (pos zero) =
  pos zero
negateInt (pos (suc n)) =
  negsuc n
negateInt (negsuc n) =
  pos (suc n)

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc n) =
  false
natEqual (suc m) zero =
  false
natEqual (suc m) (suc n) =
  natEqual m n

intEqual : Int -> Int -> Bool
intEqual (pos m) (pos n) =
  natEqual m n
intEqual (pos m) (negsuc n) =
  false
intEqual (negsuc m) (pos n) =
  false
intEqual (negsuc m) (negsuc n) =
  natEqual m n

Polynomial : Set
Polynomial =
  List Int

addPolynomial : Polynomial -> Polynomial -> Polynomial
addPolynomial [] q =
  q
addPolynomial p [] =
  p
addPolynomial (a ∷ p) (b ∷ q) =
  addInt a b ∷ addPolynomial p q

scalePolynomial : Int -> Polynomial -> Polynomial
scalePolynomial c [] =
  []
scalePolynomial c (a ∷ p) =
  multiplyInt c a ∷ scalePolynomial c p

multiplyPolynomial : Polynomial -> Polynomial -> Polynomial
multiplyPolynomial [] q =
  []
multiplyPolynomial (a ∷ p) q =
  addPolynomial
    (scalePolynomial a q)
    (pos zero ∷ multiplyPolynomial p q)

oneN : Nat
oneN =
  suc zero

onePolynomial : Polynomial
onePolynomial =
  pos oneN ∷ []

linearFactor : Int -> Polynomial
linearFactor root =
  negateInt root ∷ pos oneN ∷ []

polynomialFromRoots : (Fin5 -> Int) -> Polynomial
polynomialFromRoots roots =
  multiplyPolynomial
    (linearFactor (roots i0))
    (multiplyPolynomial
      (linearFactor (roots i1))
      (multiplyPolynomial
        (linearFactor (roots i2))
        (multiplyPolynomial
          (linearFactor (roots i3))
          (multiplyPolynomial
            (linearFactor (roots i4))
            onePolynomial))))

nonzeroCoefficientCount : Polynomial -> Nat
nonzeroCoefficientCount [] =
  zero
nonzeroCoefficientCount (coefficient ∷ coefficients)
  with intEqual coefficient (pos zero)
... | true =
  nonzeroCoefficientCount coefficients
... | false =
  suc (nonzeroCoefficientCount coefficients)

solution : Fin5 -> Int
solution i0 =
  negsuc oneN
solution i1 =
  negsuc zero
solution i2 =
  pos zero
solution i3 =
  pos oneN
solution i4 =
  pos (suc oneN)

putnam-1985-b1 : Set
putnam-1985-b1 =
  Injective solution
  and
  ((roots : Fin5 -> Int) ->
    Injective roots ->
    nonzeroCoefficientCount (polynomialFromRoots solution)
    <=N
    nonzeroCoefficientCount (polynomialFromRoots roots))
