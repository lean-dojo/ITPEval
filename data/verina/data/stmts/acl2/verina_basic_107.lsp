;; Statement-only formalization of VERINA corpus artifact verina_basic_107,
;; catalog title "ComputeAvg": a deterministic integer program computes
;; (a + b) divided by 2 using integer division, with its exact
;; quotient-and-remainder correctness contract. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Int binder domains remain explicit in
;; the final correctness statement.

(defun verina-basic-107-compute-avg-precond (a b)
  (declare (ignore a b))
  t)

;; With positive divisor 2, ACL2 FLOOR is Lean Int division: the Euclidean
;; quotient whose remainder is nonnegative and less than 2. The proof-valued
;; precondition argument is computationally irrelevant and is erased.

(defun verina-basic-107-compute-avg (a b)
  (floor (+ a b) 2))

;; ACL2 MOD by positive 2 is the same Euclidean remainder as Lean Int modulo.

(defun verina-basic-107-compute-avg-postcond
    (a b result)
  (and
   (integerp a)
   (integerp b)
   (integerp result)
   (equal
    (* 2 result)
    (-
     (+ a b)
     (mod (+ a b) 2)))))

;; This predicate is the unproved final correctness proposition. It preserves
;; both arbitrary Int inputs and the True precondition, and applies the
;; complete postcondition to the exact executable result.

(defun verina-basic-107-compute-avg-spec-satisfied-statement
    (a b)
  (implies
   (and
    (integerp a)
    (integerp b)
    (verina-basic-107-compute-avg-precond a b))
   (verina-basic-107-compute-avg-postcond
    a
    b
    (verina-basic-107-compute-avg a b))))

(value-triple :itpeval-statement-checked)
:q
