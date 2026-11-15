;; Statement-only formalization of VERINA corpus artifact verina_basic_8,
;; catalog title "myMin": a deterministic integer program returns the minimum
;; of two integers, with a result no greater than either input and equal to one
;; of them. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The two Int input domains remain explicit
;; in the final correctness proposition.

(defun verina-basic-8-my-min-precond (a b)
  (declare (ignore a b))
  t)

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. This conditional exactly preserves the source implementation,
;; including its choice of a when the inputs are equal.

(defun verina-basic-8-my-min (a b)
  (if (<= a b)
      a
    b))

;; The explicit integer predicates preserve the source Int types. The remaining
;; conjuncts are exactly the source postcondition.

(defun verina-basic-8-my-min-postcond (a b result)
  (and
   (integerp a)
   (integerp b)
   (integerp result)
   (and
    (<= result a)
    (<= result b))
   (or
    (equal result a)
    (equal result b))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over all integer inputs satisfying the source True precondition and applies
;; the complete postcondition to the exact executable result.

(defun-sk verina-basic-8-my-min-spec-satisfied-statement ()
  (forall (a b)
    (implies
     (and
      (integerp a)
      (integerp b)
      (verina-basic-8-my-min-precond a b))
     (verina-basic-8-my-min-postcond
      a
      b
      (verina-basic-8-my-min a b)))))

(value-triple :itpeval-statement-checked)
:q
