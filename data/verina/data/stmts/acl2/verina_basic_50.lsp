;; Statement-only formalization of VERINA corpus artifact verina_basic_50,
;; catalog title "Abs": a deterministic integer program returns its input
;; when nonnegative and its additive inverse when negative. This file contains
;; no proof.

(in-package "ACL2")

;; The source precondition is True. The Int input domain remains explicit in
;; the final correctness proposition.

(defun verina-basic-50-abs-precond (x)
  (declare (ignore x))
  t)

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. On every integer this conditional is exactly the source
;; executable implementation.

(defun verina-basic-50-abs (x)
  (if (< x 0)
      (- x)
    x))

;; The explicit integer predicates preserve the source Int types. The two
;; implications are the complete source postcondition.

(defun verina-basic-50-abs-postcond (x result)
  (and
   (integerp x)
   (integerp result)
   (implies
    (>= x 0)
    (equal x result))
   (implies
    (< x 0)
    (equal (+ x result) 0))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every integer input satisfying the source True precondition and applies
;; the complete postcondition to the exact executable result.

(defun-sk verina-basic-50-abs-spec-satisfied-statement ()
  (forall (x)
    (implies
     (and
      (integerp x)
      (verina-basic-50-abs-precond x))
     (verina-basic-50-abs-postcond
      x
      (verina-basic-50-abs x)))))

(value-triple :itpeval-statement-checked)
:q
