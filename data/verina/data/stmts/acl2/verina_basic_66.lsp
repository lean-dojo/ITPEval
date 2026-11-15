;; Statement-only formalization of VERINA corpus artifact verina_basic_66,
;; catalog title "ComputeIsEven": a deterministic integer program tests
;; remainder modulo two and returns true exactly for integer multiples of two.
;; This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Int input domain remains explicit in
;; the final correctness proposition.

(defun verina-basic-66-compute-is-even-precond (x)
  (declare (ignore x))
  t)

;; For every integer input, ACL2 MOD with positive divisor two agrees with
;; Lean integer remainder. This conditional therefore preserves the exact
;; executable Boolean computation. The proof-valued precondition argument is
;; computationally irrelevant and is erased.

(defun verina-basic-66-compute-is-even (x)
  (if (equal (mod x 2) 0)
      t
    nil))

(defun verina-basic-66-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; This predicate preserves the source postcondition's existential quantifier
;; over the complete integer domain.

(defun-sk verina-basic-66-has-double-witness-p (x)
  (exists (k)
    (and
     (integerp k)
     (equal x (* 2 k)))))

(defun verina-basic-66-compute-is-even-postcond
    (x result)
  (and
   (integerp x)
   (verina-basic-66-bool-p result)
   (iff
    (equal result t)
    (verina-basic-66-has-double-witness-p x))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every integer input, assumes exactly the source True precondition, and
;; applies the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-66-compute-is-even-spec-satisfied-statement
    ()
  (forall (x)
    (implies
     (and
      (integerp x)
      (verina-basic-66-compute-is-even-precond x))
     (verina-basic-66-compute-is-even-postcond
      x
      (verina-basic-66-compute-is-even x)))))

(value-triple :itpeval-statement-checked)
:q
