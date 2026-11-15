-- Statement-only formalization of PutnamBench corpus artifact putnam_1973_b3:
-- a prime-valued quadratic condition on the natural interval below p implies
-- existence and uniqueness of a reduced integer quadratic-form triple with
-- discriminant 1 - 4p. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=N_ _<N_ _<=Z_ _<Z_
infixr 3 _and_
infixr 2 _or_

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

record ExistsUnique (A : Set) (P : A -> Set) : Set where
  constructor uniqueWitness
  field
    value      : A
    property   : P value
    uniqueness : (other : A) -> P other -> other == value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

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

intSuccessor : Int -> Int
intSuccessor (pos n) =
  pos (suc n)
intSuccessor (negsuc zero) =
  pos zero
intSuccessor (negsuc (suc n)) =
  negsuc n

_<Z_ : Int -> Int -> Set
x <Z y =
  intSuccessor x <=Z y

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

negateInt : Int -> Int
negateInt (pos n) =
  negative n
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

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

squareInt : Int -> Int
squareInt x =
  multiplyInt x x

Divides : Nat -> Nat -> Set
Divides divisor number =
  Exists Nat
    (\ factor -> divisor * factor == number)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

Prime : Nat -> Set
Prime number =
  twoN <=N number
  and
  ((divisor : Nat) ->
    Divides divisor number ->
    divisor == oneN or divisor == number)

record Triple : Set where
  constructor triple
  field
    first-coordinate  : Int
    second-coordinate : Int
    third-coordinate  : Int

open Triple

oneZ : Int
oneZ =
  pos oneN

fourZ : Int
fourZ =
  pos (suc (suc twoN))

Positive : Int -> Set
Positive x =
  pos zero <Z x

ReducedTriple : Nat -> Triple -> Set
ReducedTriple p coefficients =
  subtractInt
    (squareInt (second-coordinate coefficients))
    (multiplyInt
      fourZ
      (multiplyInt
        (first-coordinate coefficients)
        (third-coordinate coefficients)))
  ==
  subtractInt
    oneZ
    (multiplyInt fourZ (pos p))
  and
  Positive (first-coordinate coefficients)
  and
  first-coordinate coefficients <=Z third-coordinate coefficients
  and
  negateInt (first-coordinate coefficients) <=Z
    second-coordinate coefficients
  and
  second-coordinate coefficients <Z first-coordinate coefficients

putnam-1973-b3 : Set
putnam-1973-b3 =
  (p : Nat) ->
  oneN <N p ->
  ((x : Nat) ->
    x <N p ->
    Prime (x * x - x + p)) ->
  ExistsUnique Triple (ReducedTriple p)
