-- Statement-only formalization of NTP4VC corpus artifact
-- frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_trace_pos_post_goal12:
-- the positive-trace branch verification condition for converting a real
-- rotation matrix stored in float memory to a quaternion. This file contains no proof.

{-# OPTIONS --safe #-}

module float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_trace_pos_post_goal12 where

open import Agda.Builtin.Bool using (Bool; false; true)
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

IfSet : Set -> Set -> Set -> Set
IfSet condition whenTrue whenFalse =
  (condition -> whenTrue) and (Not condition -> whenFalse)

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

natEqual : Nat -> Nat -> Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

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

intEqual : Int -> Int -> Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos m) (negsuc n) = false
intEqual (negsuc m) (pos n) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

twoN fourN : Nat
twoN = suc (suc zero)
fourN = suc (suc twoN)

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
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

    square-root-nonnegative :
      (x : R) -> lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual zeroR x ->
      multiply (squareRoot x) (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      squareRoot x == zeroR
    square-root-unique :
      (x y : R) ->
      lessOrEqual zeroR y ->
      multiply y y == x ->
      y == squareRoot x

open CompleteOrderedRealField

StrictLess :
  {R : Set} -> CompleteOrderedRealField R -> R -> R -> Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

subtract :
  {R : Set} -> CompleteOrderedRealField R -> R -> R -> R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} -> CompleteOrderedRealField R -> R -> R -> R
divide reals x y =
  multiply reals x (inverse reals y)

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr -> Int -> Addr
shift (addr b o) k =
  addr b (addInt o k)

addrEqual : Addr -> Addr -> Bool
addrEqual (addr b o) (addr b' o') with intEqual b b'
... | false = false
... | true = intEqual o o'

ifBool : {A : Set} -> Bool -> A -> A -> A
ifBool true whenTrue whenFalse = whenTrue
ifBool false whenTrue whenFalse = whenFalse

update : {A : Set} -> (Addr -> A) -> Addr -> A -> Addr -> A
update memory location value query =
  ifBool (addrEqual query location) value (memory query)

MapEq : {A B : Set} -> (A -> B) -> (A -> B) -> Set
MapEq {A = A} f g =
  (x : A) -> f x == g x

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

record RealQuat (R : Set) : Set where
  constructor realQuat
  field
    qi qx qy qz : R

open RealQuat

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

quatEq : {R : Set} -> RealQuat R -> RealQuat R -> Set
quatEq x y =
  qi x == qi y and
  qx x == qx y and
  qy x == qy y and
  qz x == qz y

module Definitions {R : Set} (reals : CompleteOrderedRealField R) where

  zeroReal oneReal twoReal fourReal halfReal quarterReal : R
  zeroReal = zeroR reals
  oneReal = oneR reals
  twoReal = fromNat reals twoN
  fourReal = fromNat reals fourN
  halfReal = divide reals oneReal twoReal
  quarterReal = divide reals oneReal fourReal

  plus : R -> R -> R
  plus = add reals

  times : R -> R -> R
  times = multiply reals

  minus : R -> R -> R
  minus = subtract reals

  quotient : R -> R -> R
  quotient = divide reals

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

  traceMemory : (Addr -> R) -> Addr -> R
  traceMemory memory p =
    let m = readRMat memory p
    in plus (plus (a00 m) (a11 m)) (a22 m)

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

  tracePositiveQuat : (Addr -> R) -> Addr -> RealQuat R
  tracePositiveQuat memory p =
    let m = transpose (readRMat memory p)
        trace = plus (plus (a00 m) (a11 m)) (a22 m)
        scale = quotient halfReal (squareRoot reals (plus oneReal trace))
    in realQuat
      (quotient quarterReal scale)
      (times (minus (a21 m) (a12 m)) scale)
      (times (minus (a02 m) (a20 m)) scale)
      (times (minus (a10 m) (a01 m)) scale)

  quatOfFloatQuat : (Addr -> R) -> Addr -> RealQuat R
  quatOfFloatQuat memory p =
    realQuat
      (memory (shift p zeroZ))
      (memory (shift p oneZ))
      (memory (shift p twoZ))
      (memory (shift p threeZ))

module Goal
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (memoryModel : MemoryModel) where

  open Definitions reals

  goal12 : Set
  goal12 =
    (t1 : Addr -> R) ->
    (a a1 : Addr) ->
    (t8 : Addr -> R) ->
    (r3 r7 : R) ->
    (t7 : Addr -> R) ->
    (r6 r2 : R) ->
    (t4 : Addr -> R) ->
    (r1 : R) ->
    (t6 : Addr -> R) ->
    (r5 r : R) ->
    (t5 : Addr -> R) ->
    (r4 : R) ->
    (allocation : Int -> Int) ->
    (t9 t2 t3 : Addr -> R) ->
    let a2 = readRMat t1 a
        a3 = shift a zeroZ
        a4 = shift a3 zeroZ
        r8 = t1 a4
        a5 = shift a3 fourZ
        r9 = t1 a5
        a6 = shift a3 eightZ
        r10 = t1 a6
        r11 = plus (plus r8 r9) r10
        a7 = shift a1 zeroZ
        m = update t8 a7 (times halfReal r3)
        a8 = shift a1 oneZ
        a9 = shift a3 fiveZ
        a10 = shift a3 sevenZ
        m1 = update m a8 (quotient (minus (m a9) (m a10)) r7)
        a11 = shift a1 twoZ
        a12 = shift a3 sixZ
        a13 = shift a3 twoZ
        m2 = update m1 a11 (quotient (minus (m1 a12) (m1 a13)) r7)
        a14 = shift a1 threeZ
        a15 = shift a3 oneZ
        a16 = shift a3 threeZ
        r13 = plus oneReal (plus (plus (t8 a4) (t8 a5)) (t8 a6))
        m3 = update
          (update t7 a7 (quotient (minus (t7 a9) (t7 a10)) r6))
          a8 (times halfReal r2)
        m4 = update m3 a11 (quotient (plus (m3 a15) (m3 a16)) r6)
        r15 = plus (minus (minus (t7 a4) (t7 a5)) (t7 a6)) oneReal
        r16 = t4 a6
        r17 = t4 a5
        r19 = times twoReal r1
        m5 = update t6 a7 (quotient (minus (t6 a12) (t6 a13)) r5)
        m6 = update
          (update m5 a8 (quotient (plus (m5 a15) (m5 a16)) r5))
          a11 (times halfReal r1)
        m7 = update m6 a14 (quotient (plus (m6 a9) (m6 a10)) r5)
        r20 = plus (minus (minus (t6 a5) (t6 a4)) (t6 a6)) oneReal
        r22 = times twoReal r
        m8 = update t5 a7 (quotient (minus (t5 a15) (t5 a16)) r4)
        m9 = update m8 a8 (quotient (plus (m8 a12) (m8 a13)) r4)
        m10 = update
          (update m9 a11 (quotient (plus (m9 a9) (m9 a10)) r4))
          a14 (times halfReal r)
        r23 = plus (minus (minus (t5 a6) (t5 a4)) (t5 a5)) oneReal
        final0 =
          MapEq t8 t1 and
          times twoReal r3 == r7 and
          MapEq
            (update m2 a14 (quotient (minus (m2 a15) (m2 a16)) r7))
            t9 and
          le zeroReal r3 and
          le zeroReal r13 and
          IsFinite32 r3 and
          IsFinite32 r13
        final1 =
          MapEq t7 t3 and
          times twoReal r2 == r6 and
          MapEq
            (update m4 a14 (quotient (plus (m4 a12) (m4 a13)) r6))
            t9 and
          le zeroReal r2 and
          le zeroReal r15 and
          IsFinite32 r2 and
          IsFinite32 r15
        final2 =
          MapEq t6 t4 and
          r19 == r5 and
          MapEq m7 t9 and
          le zeroReal r1 and
          le zeroReal r20 and
          IsFinite32 r1 and
          IsFinite32 r20
        final3 =
          MapEq t5 t4 and
          r22 == r4 and
          MapEq m10 t9 and
          le zeroReal r and
          le zeroReal r23 and
          IsFinite32 r and
          IsFinite32 r23
        lastBranch = IfSet (lt r16 r17) final2 final3
        branchWithA11 =
          MapEq t3 t2 and
          IfSet (lt (t3 a6) (t3 a4))
            final1
            (MapEq t4 t3 and lastBranch)
        nonTraceBranch =
          MapEq t2 t1 and
          IfSet (lt (t2 a5) (t2 a4))
            branchWithA11
            (MapEq t4 t2 and lastBranch)
        pathCondition = IfSet (lt zeroReal r11) final0 nonTraceBranch
    in
    lt zeroReal (traceMemory t1 a) ->
    region memoryModel (base a) <=Z zeroZ ->
    region memoryModel (base a1) <=Z zeroZ ->
    linked memoryModel allocation ->
    IsFloat32 r ->
    IsFloat32 r1 ->
    IsFloat32 r2 ->
    IsFloat32 r3 ->
    IsFloat32 r4 ->
    IsFloat32 r5 ->
    IsFloat32 r6 ->
    IsFloat32 r7 ->
    validRw allocation a1 fourZ ->
    rvalidFloatRMat allocation t1 a ->
    separated a nineZ a1 fourZ ->
    rotationMatrix a2 ->
    specialOrthogonal a2 ->
    IsFloat32 r8 ->
    IsFloat32 r9 ->
    IsFloat32 r10 ->
    IsFloat32 r11 ->
    pathCondition ->
    r3 == squareRoot reals r13 ->
    quatEq
      (tracePositiveQuat t9 a)
      (quatOfFloatQuat t9 a1)

float-quat-of-rmat-trace-pos-post-goal12 : Set1
float-quat-of-rmat-trace-pos-post-goal12 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (memoryModel : MemoryModel) ->
  Goal.goal12 reals memoryModel
