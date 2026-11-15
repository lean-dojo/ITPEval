;; Statement-only formalization of VERINA corpus artifact verina_basic_53,
;; catalog title "CalSum": a deterministic natural-number recursion computes
;; the sum from one through N and satisfies the standard doubled triangular-
;; number identity. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Nat input domain remains explicit in
;; the final correctness proposition.

(defun verina-basic-53-cal-sum-precond (n)
  (declare (ignore n))
  t)

;; This is the source-local LOOP recursion. Zero returns zero; every positive
;; natural N adds N to the result at N - 1. The proof-valued precondition
;; argument to CalSum is computationally irrelevant and is erased.

(defun verina-basic-53-cal-sum-loop (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ n
       (verina-basic-53-cal-sum-loop
        (- n 1)))))

(defun verina-basic-53-cal-sum (n)
  (verina-basic-53-cal-sum-loop n))

;; This is the complete source postcondition, with both Nat binder domains
;; represented explicitly.

(defun verina-basic-53-cal-sum-postcond (n result)
  (and
   (natp n)
   (natp result)
   (equal
    (* 2 result)
    (* n (+ n 1)))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every natural input, assumes exactly the source True precondition, and
;; applies the complete postcondition to the exact executable result.

(defun-sk verina-basic-53-cal-sum-spec-satisfied-statement ()
  (forall (n)
    (implies
     (and
      (natp n)
      (verina-basic-53-cal-sum-precond n))
     (verina-basic-53-cal-sum-postcond
      n
      (verina-basic-53-cal-sum n)))))

(value-triple :itpeval-statement-checked)
:q
