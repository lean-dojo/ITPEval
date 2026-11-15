;; Statement-only formalization of VERINA corpus artifact verina_basic_65,
;; catalog title "SquareRoot": a deterministic bounded natural-number search
;; computes the integer square root characterized by consecutive squares.
;; This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Nat input domain remains explicit in
;; the final correctness proposition.

(defun verina-basic-65-square-root-precond (n)
  (declare (ignore n))
  t)

;; This is the source-local BOUNDEDLOOP recursion. Zero fuel returns the
;; current candidate. Positive fuel increments the candidate exactly when its
;; next square is at most N, then recurs with predecessor fuel; otherwise it
;; returns the current candidate immediately.

(defun verina-basic-65-bounded-loop (n bound r)
  (declare (xargs :measure (nfix bound)))
  (if (zp bound)
      r
    (if (<= (* (+ r 1) (+ r 1)) n)
        (verina-basic-65-bounded-loop
         n
         (- bound 1)
         (+ r 1))
      r)))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. Starting from zero with N+1 units of fuel reproduces the
;; complete executable Lean implementation.

(defun verina-basic-65-square-root (n)
  (verina-basic-65-bounded-loop n (+ n 1) 0))

;; This is the complete source postcondition over Nat: RESULT is the greatest
;; natural whose square is at most N, expressed by the same two inequalities.

(defun verina-basic-65-square-root-postcond (n result)
  (and
   (natp n)
   (natp result)
   (<= (* result result) n)
   (< n (* (+ result 1) (+ result 1)))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every natural input, assumes exactly the source True precondition, and
;; applies the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-65-square-root-spec-satisfied-statement
    ()
  (forall (n)
    (implies
     (and
      (natp n)
      (verina-basic-65-square-root-precond n))
     (verina-basic-65-square-root-postcond
      n
      (verina-basic-65-square-root n)))))

(value-triple :itpeval-statement-checked)
:q
