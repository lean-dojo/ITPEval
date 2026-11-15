-- Statement-only formalization of Thousand Theorems artifact Q656772
-- (thousand-theorems__lean4__Q656772), "Cayley–Hamilton theorem": over any
-- commutative ring, evaluating a square matrix's characteristic polynomial at
-- the matrix itself gives the zero matrix. This file contains no proof.

universe u v

namespace Q656772

/-- A bundled commutative ring, including exactly the algebraic laws used by the theorem. -/
structure CommRing (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

/-- A permutation of an arbitrary type. -/
structure Perm (ι : Type v) where
  toFun : ι → ι
  invFun : ι → ι
  leftInv : ∀ i, invFun (toFun i) = i
  rightInv : ∀ i, toFun (invFun i) = i

/-- The entries of a list are pairwise distinct. -/
def NoDup {α : Type u} : List α → Prop
  | [] => True
  | x :: xs => (∀ y, List.Mem y xs → x ≠ y) ∧ NoDup xs

/--
An explicit presentation of an arbitrary finite index type and its finite permutation group.
The completeness and no-duplication fields ensure that neither carrier is bounded or sampled.
-/
structure FiniteIndex (ι : Type v) where
  elems : List ι
  elems_nodup : NoDup elems
  elems_complete : ∀ i, List.Mem i elems
  perms : List (Perm ι)
  perms_nodup : NoDup perms
  perms_complete : ∀ σ, List.Mem σ perms

/-- A square matrix over an arbitrary carrier. -/
abbrev Matrix (ι : Type v) (R : Type u) := ι → ι → R

/-- Coefficient-list polynomials, with coefficients in increasing degree order. -/
abbrev Polynomial (R : Type u) := List R

def ringSum {R : Type u} (r : CommRing R) : List R → R
  | [] => r.zero
  | x :: xs => r.add x (ringSum r xs)

def ringProduct {R : Type u} (r : CommRing R) : List R → R
  | [] => r.one
  | x :: xs => r.mul x (ringProduct r xs)

def indexOf {ι : Type v} [DecidableEq ι] (x : ι) : List ι → Nat
  | [] => 0
  | y :: ys => if x = y then 0 else Nat.succ (indexOf x ys)

def countLess (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if y < x then 1 else 0) + countLess x ys

def inversionCount : List Nat → Nat
  | [] => 0
  | x :: xs => countLess x xs + inversionCount xs

def permutationInversions {ι : Type v} [DecidableEq ι]
    (idx : FiniteIndex ι) (σ : Perm ι) : Nat :=
  inversionCount (idx.elems.map (fun i => indexOf (σ.toFun i) idx.elems))

def polyAdd {R : Type u} (r : CommRing R) :
    Polynomial R → Polynomial R → Polynomial R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => r.add a b :: polyAdd r p q

def polyNeg {R : Type u} (r : CommRing R) : Polynomial R → Polynomial R
  | [] => []
  | a :: p => r.neg a :: polyNeg r p

def polySub {R : Type u} (r : CommRing R) (p q : Polynomial R) : Polynomial R :=
  polyAdd r p (polyNeg r q)

def polyScale {R : Type u} (r : CommRing R) (a : R) : Polynomial R → Polynomial R
  | [] => []
  | b :: p => r.mul a b :: polyScale r a p

def polyShift {R : Type u} (r : CommRing R) : Polynomial R → Polynomial R
  | [] => []
  | p => r.zero :: p

def polyMul {R : Type u} (r : CommRing R) :
    Polynomial R → Polynomial R → Polynomial R
  | [], _ => []
  | a :: p, q =>
      polyAdd r (polyScale r a q) (polyShift r (polyMul r p q))

def polySum {R : Type u} (r : CommRing R) : List (Polynomial R) → Polynomial R
  | [] => []
  | p :: ps => polyAdd r p (polySum r ps)

def polyProduct {R : Type u} (r : CommRing R) :
    List (Polynomial R) → Polynomial R
  | [] => [r.one]
  | p :: ps => polyMul r p (polyProduct r ps)

def polyConst {R : Type u} (a : R) : Polynomial R :=
  [a]

def polyX {R : Type u} (r : CommRing R) : Polynomial R :=
  [r.zero, r.one]

def signedPolynomial {R : Type u} (r : CommRing R) (inversions : Nat)
    (p : Polynomial R) : Polynomial R :=
  if inversions % 2 = 0 then p else polyNeg r p

/-- The Leibniz determinant of a polynomial-valued square matrix. -/
def polynomialDeterminant {R : Type u} {ι : Type v} [DecidableEq ι]
    (r : CommRing R) (idx : FiniteIndex ι) (A : Matrix ι (Polynomial R)) :
    Polynomial R :=
  polySum r <| idx.perms.map fun σ =>
    signedPolynomial r (permutationInversions idx σ)
      (polyProduct r (idx.elems.map fun i => A (σ.toFun i) i))

/-- The characteristic matrix `X I - M`. -/
def charmatrix {R : Type u} {ι : Type v} [DecidableEq ι]
    (r : CommRing R) (M : Matrix ι R) : Matrix ι (Polynomial R) :=
  fun i j =>
    if i = j then
      polySub r (polyX r) (polyConst (M i j))
    else
      polyNeg r (polyConst (M i j))

/-- The characteristic polynomial `det (X I - M)`. -/
def charpoly {R : Type u} {ι : Type v} [DecidableEq ι]
    (r : CommRing R) (idx : FiniteIndex ι) (M : Matrix ι R) : Polynomial R :=
  polynomialDeterminant r idx (charmatrix r M)

def zeroMatrix {R : Type u} {ι : Type v} (r : CommRing R) : Matrix ι R :=
  fun _ _ => r.zero

def scalarMatrix {R : Type u} {ι : Type v} [DecidableEq ι]
    (r : CommRing R) (a : R) : Matrix ι R :=
  fun i j => if i = j then a else r.zero

def matrixAdd {R : Type u} {ι : Type v} (r : CommRing R)
    (A B : Matrix ι R) : Matrix ι R :=
  fun i j => r.add (A i j) (B i j)

def matrixMul {R : Type u} {ι : Type v} (r : CommRing R)
    (idx : FiniteIndex ι) (A B : Matrix ι R) : Matrix ι R :=
  fun i j => ringSum r (idx.elems.map fun k => r.mul (A i k) (B k j))

/-- Horner evaluation of a scalar polynomial at a square matrix. -/
def matrixEval {R : Type u} {ι : Type v} [DecidableEq ι]
    (r : CommRing R) (idx : FiniteIndex ι) (M : Matrix ι R) :
    Polynomial R → Matrix ι R
  | [] => zeroMatrix r
  | a :: p =>
      matrixAdd r (scalarMatrix r a) (matrixMul r idx M (matrixEval r idx M p))

/-- The Cayley–Hamilton theorem for square matrices over an arbitrary commutative ring. -/
theorem aeval_self_charpoly {R : Type u} {ι : Type v}
    (r : CommRing R) [DecidableEq ι] (idx : FiniteIndex ι) (M : Matrix ι R) :
    matrixEval r idx M (charpoly r idx M) = zeroMatrix r := sorry

end Q656772
