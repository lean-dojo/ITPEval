;; Statement-only formalization of VERINA corpus artifact verina_basic_5,
;; catalog title "multiply": a deterministic integer program returns the
;; product of its two integer inputs, with the specified zero-difference
;; postcondition. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The two Int binder domains remain explicit
;; in the final correctness proposition.

(defun verina-basic-5-multiply-precond (a b)
  (declare (ignore a b))
  t)

;; The proof-valued precondition argument has no computational effect and is
;; erased. This is exactly the source computation a * b.

(defun verina-basic-5-multiply (a b)
  (* a b))

;; This preserves both conjuncts of the source postcondition.

(defun verina-basic-5-multiply-postcond (a b result)
  (and
   (integerp a)
   (integerp b)
   (integerp result)
   (equal (- result (* a b)) 0)
   (equal (- (* a b) result) 0)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over both complete Int domains, applies the True precondition, and connects
;; the complete postcondition to the exact executable result.

(defun-sk verina-basic-5-multiply-spec-satisfied-statement ()
  (forall (a b)
    (implies
     (and
      (integerp a)
      (integerp b)
      (verina-basic-5-multiply-precond a b))
     (verina-basic-5-multiply-postcond
      a
      b
      (verina-basic-5-multiply a b)))))

(value-triple :itpeval-statement-checked)
:q
