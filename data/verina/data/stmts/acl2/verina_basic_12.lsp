;; Statement-only formalization of VERINA corpus artifact verina_basic_12,
;; catalog title "cubeSurfaceArea": a deterministic natural-number program
;; computes six times the square of a cube's edge length, with the source
;; truncated-subtraction correctness contract. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Nat binder domain remains explicit in
;; the final correctness statement.

(defun verina-basic-12-cube-surface-area-precond (size)
  (declare (ignore size))
  t)

;; The proof-valued precondition argument has no computational effect and is
;; erased. On natural inputs this is exactly the source computation
;; 6 * size * size.

(defun verina-basic-12-cube-surface-area (size)
  (* (* 6 size) size))

;; Lean Nat subtraction is truncated at zero.

(defun verina-basic-12-nat-sub (left right)
  (nfix (- left right)))

(defun verina-basic-12-cube-surface-area-postcond
    (size result)
  (and
   (natp size)
   (natp result)
   (equal
    (verina-basic-12-nat-sub
     result
     (* (* 6 size) size))
    0)
   (equal
    (verina-basic-12-nat-sub
     (* (* 6 size) size)
     result)
    0)))

;; This predicate is the unproved final correctness proposition. Its antecedent
;; preserves the Nat input and True precondition, and its conclusion applies
;; the complete postcondition to the exact executable result.

(defun verina-basic-12-cube-surface-area-spec-satisfied-statement
    (size)
  (implies
   (and
    (natp size)
    (verina-basic-12-cube-surface-area-precond size))
   (verina-basic-12-cube-surface-area-postcond
    size
    (verina-basic-12-cube-surface-area size))))

(value-triple :itpeval-statement-checked)
:q
