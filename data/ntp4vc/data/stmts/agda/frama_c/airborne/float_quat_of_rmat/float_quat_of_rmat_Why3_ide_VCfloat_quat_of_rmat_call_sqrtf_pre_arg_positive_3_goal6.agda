-- Statement-only formalization of NTP4VC corpus artifact
-- frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_call_sqrtf_pre_arg_positive_3_goal6:
-- the positivity precondition for the square-root argument in the third
-- branch of float rotation-matrix to quaternion conversion. This file contains no proof.

{-# OPTIONS --safe #-}

module FloatQuatOfRMatGoal6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _!=_ _<=N_ _<=Z_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Top : Set where
  constructor top

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

negativeNat : Nat -> Int
negativeNat zero = pos zero
negativeNat (suc n) = negsuc n

differenceNat : Nat -> Nat -> Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

_<=Z_ : Int -> Int -> Set
pos m <=Z pos n = m <=N n
pos m <=Z negsuc n = Bottom
negsuc m <=Z pos n = Top
negsuc m <=Z negsuc n = n <=N m

IntLess : Int -> Int -> Set
IntLess x y = (x <=Z y) and (x != y)

zeroZ oneZ twoZ threeZ fourZ fiveZ sixZ sevenZ eightZ nineZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))
fourZ = pos (suc (suc (suc (suc zero))))
fiveZ = pos (suc (suc (suc (suc (suc zero)))))
sixZ = pos (suc (suc (suc (suc (suc (suc zero))))))
sevenZ = pos (suc (suc (suc (suc (suc (suc (suc zero)))))))
eightZ = pos (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
nineZ = pos (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

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
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR
    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) == add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) -> x != zeroR -> multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y -> lessOrEqual y z -> lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y -> lessOrEqual y x -> x == y
    order-total :
      (x y : R) -> lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y -> lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and oneR != zeroR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) -> fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Σ Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Σ R P ->
      Σ R
        (\ upper -> (x : R) -> P x -> lessOrEqual x upper) ->
      Σ R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum) and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

StrictLess :
  {R : Set} -> CompleteOrderedRealField R -> R -> R -> Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

subtract :
  {R : Set} -> CompleteOrderedRealField R -> R -> R -> R
subtract reals x y =
  add reals x (negate reals y)

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr -> Int -> Addr
shift (addr b o) k =
  addr b (addInt o k)

record MemoryModel : Set1 where
  field
    region : Int -> Int
    linked : (Int -> Int) -> Set

open MemoryModel

validRw : (Int -> Int) -> Addr -> Int -> Set
validRw allocation p n =
  IntLess zeroZ n ->
  IntLess zeroZ (base p) and
  (zeroZ <=Z offset p) and
  (addInt (offset p) n <=Z allocation (base p))

validRd : (Int -> Int) -> Addr -> Int -> Set
validRd allocation p n =
  IntLess zeroZ n ->
  zeroZ != base p and
  (zeroZ <=Z offset p) and
  (addInt (offset p) n <=Z allocation (base p))

separated : Addr -> Int -> Addr -> Int -> Set
separated p a q b =
  (a <=Z zeroZ) or
  (b <=Z zeroZ) or
  (base p != base q) or
  (addInt (offset q) b <=Z offset p) or
  (addInt (offset p) a <=Z offset q)

IsFloat32 : {R : Set} -> R -> Set
IsFloat32 x = Top

IsFinite32 : {R : Set} -> R -> Set
IsFinite32 x = Top

record RealRMat (R : Set) : Set where
  constructor realRMat
  field
    a00 a01 a02 : R
    a10 a11 a12 : R
    a20 a21 a22 : R

open RealRMat

matrixEq : {R : Set} -> RealRMat R -> RealRMat R -> Set
matrixEq x y =
  a00 x == a00 y and
  a01 x == a01 y and
  a02 x == a02 y and
  a10 x == a10 y and
  a11 x == a11 y and
  a12 x == a12 y and
  a20 x == a20 y and
  a21 x == a21 y and
  a22 x == a22 y

module Definitions {R : Set} (reals : CompleteOrderedRealField R) where

  zeroReal oneReal : R
  zeroReal = zeroR reals
  oneReal = oneR reals

  plus : R -> R -> R
  plus = add reals

  times : R -> R -> R
  times = multiply reals

  neg : R -> R
  neg = negate reals

  minus : R -> R -> R
  minus = subtract reals

  le : R -> R -> Set
  le = lessOrEqual reals

  lt : R -> R -> Set
  lt = StrictLess reals

  readRMat : (Addr -> R) -> Addr -> RealRMat R
  readRMat memory p =
    realRMat
      (memory (shift p zeroZ))
      (memory (shift p oneZ))
      (memory (shift p twoZ))
      (memory (shift p threeZ))
      (memory (shift p fourZ))
      (memory (shift p fiveZ))
      (memory (shift p sixZ))
      (memory (shift p sevenZ))
      (memory (shift p eightZ))

  transpose : RealRMat R -> RealRMat R
  transpose m =
    realRMat
      (a00 m) (a10 m) (a20 m)
      (a01 m) (a11 m) (a21 m)
      (a02 m) (a12 m) (a22 m)

  matrixMultiply : RealRMat R -> RealRMat R -> RealRMat R
  matrixMultiply x y =
    realRMat
      (plus (plus (times (a00 x) (a00 y)) (times (a01 x) (a10 y)))
        (times (a02 x) (a20 y)))
      (plus (plus (times (a00 x) (a01 y)) (times (a01 x) (a11 y)))
        (times (a02 x) (a21 y)))
      (plus (plus (times (a00 x) (a02 y)) (times (a01 x) (a12 y)))
        (times (a02 x) (a22 y)))
      (plus (plus (times (a10 x) (a00 y)) (times (a11 x) (a10 y)))
        (times (a12 x) (a20 y)))
      (plus (plus (times (a10 x) (a01 y)) (times (a11 x) (a11 y)))
        (times (a12 x) (a21 y)))
      (plus (plus (times (a10 x) (a02 y)) (times (a11 x) (a12 y)))
        (times (a12 x) (a22 y)))
      (plus (plus (times (a20 x) (a00 y)) (times (a21 x) (a10 y)))
        (times (a22 x) (a20 y)))
      (plus (plus (times (a20 x) (a01 y)) (times (a21 x) (a11 y)))
        (times (a22 x) (a21 y)))
      (plus (plus (times (a20 x) (a02 y)) (times (a21 x) (a12 y)))
        (times (a22 x) (a22 y)))

  identityMatrix : RealRMat R
  identityMatrix =
    realRMat
      oneReal zeroReal zeroReal
      zeroReal oneReal zeroReal
      zeroReal zeroReal oneReal

  determinant : RealRMat R -> R
  determinant m =
    minus
      (minus
        (minus
          (plus
            (plus
              (times (times (a00 m) (a11 m)) (a22 m))
              (times (times (a01 m) (a12 m)) (a20 m)))
            (times (times (a02 m) (a10 m)) (a21 m)))
          (times (times (a00 m) (a12 m)) (a21 m)))
        (times (times (a01 m) (a10 m)) (a22 m)))
      (times (times (a02 m) (a11 m)) (a20 m))

  rotationMatrix : RealRMat R -> Set
  rotationMatrix m =
    matrixEq (matrixMultiply m (transpose m)) identityMatrix

  specialOrthogonal : RealRMat R -> Set
  specialOrthogonal m =
    determinant m == oneReal

  finiteFloatRMat : (Addr -> R) -> Addr -> Set
  finiteFloatRMat memory p =
    IsFinite32 (memory (shift p zeroZ)) and
    IsFinite32 (memory (shift p oneZ)) and
    IsFinite32 (memory (shift p twoZ)) and
    IsFinite32 (memory (shift p threeZ)) and
    IsFinite32 (memory (shift p fourZ)) and
    IsFinite32 (memory (shift p fiveZ)) and
    IsFinite32 (memory (shift p sixZ)) and
    IsFinite32 (memory (shift p sevenZ)) and
    IsFinite32 (memory (shift p eightZ))

  rvalidFloatRMat :
    (Int -> Int) -> (Addr -> R) -> Addr -> Set
  rvalidFloatRMat allocation memory p =
    finiteFloatRMat memory p and validRd allocation p nineZ

module Goal
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (memoryModel : MemoryModel) where

  open Definitions reals

  goal6 : Set
  goal6 =
    (a : Addr) ->
    (t1 : Addr -> R) ->
    (a1 : Addr) ->
    (allocation : Int -> Int) ->
    let a2 = shift a zeroZ
        r = t1 (shift a2 eightZ)
        r1 = t1 (shift a2 fourZ)
        r2 = t1 (shift a2 zeroZ)
        r3 = plus (plus r2 r1) r
        a3 = readRMat t1 a
    in
    region memoryModel (base a) <=Z zeroZ ->
    region memoryModel (base a1) <=Z zeroZ ->
    lt r r1 ->
    le r3 zeroReal ->
    linked memoryModel allocation ->
    validRw allocation a1 fourZ ->
    rvalidFloatRMat allocation t1 a ->
    separated a nineZ a1 fourZ ->
    rotationMatrix a3 ->
    specialOrthogonal a3 ->
    IsFloat32 r2 ->
    IsFloat32 (t1 (shift a2 twoZ)) ->
    IsFloat32 r1 ->
    IsFloat32 (t1 (shift a2 sixZ)) ->
    IsFloat32 r ->
    IsFloat32 r3 ->
    (le r2 r1 or le r2 r) ->
    le zeroReal
      (plus (plus (plus r1 (neg r2)) (neg r)) oneReal)

float-quat-of-rmat-call-sqrtf-pre-arg-positive-3-goal6 : Set1
float-quat-of-rmat-call-sqrtf-pre-arg-positive-3-goal6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (memoryModel : MemoryModel) ->
  Goal.goal6 reals memoryModel
