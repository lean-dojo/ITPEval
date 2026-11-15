;; Statement-only formalization of VERINA corpus artifact verina_basic_1,
;; "hasOppositeSign": a deterministic integer program returns true exactly
;; when its two inputs have opposite signs. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The two Int binder domains are explicit in
;; the final correctness statement.

(defun verina-basic-1-has-opposite-sign-precond (a b)
  (declare (ignore a b))
  t)

;; This predicate is the source postcondition's definition of opposite signs:
;; one input is strictly negative and the other is strictly positive.

(defun verina-basic-1-opposite-sign-p (a b)
  (or
   (and (< a 0)
        (< 0 b))
   (and (< 0 a)
        (< b 0))))

;; The proof-valued precondition argument has no computational effect and is
;; erased. This is exactly the source computation a * b < 0, with an ACL2
;; Boolean result.

(defun verina-basic-1-has-opposite-sign (a b)
  (if (< (* a b) 0)
      t
    nil))

(defun verina-basic-1-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

(defun verina-basic-1-has-opposite-sign-postcond
    (a b result)
  (and
   (integerp a)
   (integerp b)
   (verina-basic-1-bool-p result)
   (implies
    (verina-basic-1-opposite-sign-p a b)
    result)
   (implies
    (not (verina-basic-1-opposite-sign-p a b))
    (not result))))

;; This predicate is the unproved final correctness proposition. Its antecedent
;; preserves both Int binders and the True precondition, and its conclusion
;; applies the complete postcondition to the exact executable result.

(defun verina-basic-1-has-opposite-sign-spec-satisfied-statement
    (a b)
  (implies
   (and
    (integerp a)
    (integerp b)
    (verina-basic-1-has-opposite-sign-precond a b))
   (verina-basic-1-has-opposite-sign-postcond
    a
    b
    (verina-basic-1-has-opposite-sign a b))))

(value-triple :itpeval-statement-checked)
:q
