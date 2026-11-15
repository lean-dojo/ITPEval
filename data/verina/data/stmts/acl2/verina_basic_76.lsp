;; Statement-only formalization of VERINA corpus artifact verina_basic_76,
;; catalog title "myMin": a deterministic integer program returns x when x is
;; strictly less than y and otherwise returns y, with the contract that it
;; returns x when x <= y and y when x > y. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The two Int input domains remain explicit
;; in the final correctness proposition.

(defun verina-basic-76-my-min-precond (x y)
  (declare (ignore x y))
  t)

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. This conditional exactly preserves the source implementation,
;; including its else-branch choice when the inputs are equal.

(defun verina-basic-76-my-min (x y)
  (if (< x y)
      x
    y))

;; The explicit integer predicates preserve the source Int types. The two
;; implications are exactly the complete source postcondition.

(defun verina-basic-76-my-min-postcond (x y result)
  (and
   (integerp x)
   (integerp y)
   (integerp result)
   (implies
    (<= x y)
    (equal result x))
   (implies
    (> x y)
    (equal result y))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over all integer inputs satisfying the source True precondition and applies
;; the complete postcondition to the exact executable result.

(defun-sk verina-basic-76-my-min-spec-satisfied-statement ()
  (forall (x y)
    (implies
     (and
      (integerp x)
      (integerp y)
      (verina-basic-76-my-min-precond x y))
     (verina-basic-76-my-min-postcond
      x
      y
      (verina-basic-76-my-min x y)))))

(value-triple :itpeval-statement-checked)
:q
