;; Statement-only formalization of VERINA corpus artifact verina_basic_99,
;; catalog title "Triple": a deterministic integer program computes three times
;; its input using the source branch at x < 18 and satisfies the quotient-and-
;; divisibility contract. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Int binder domain remains explicit in
;; the final correctness proposition.

(defun verina-basic-99-triple-precond (x)
  (declare (ignore x))
  t)

;; The proof-valued precondition argument has no computational effect and is
;; erased. ACL2 FLOOR by the positive divisor 2 is Lean Int division here, and
;; the source branch and local bindings are retained exactly.

(defun verina-basic-99-triple (x)
  (if (< x 18)
      (let* ((a (* 2 x))
             (b (* 4 x)))
        (floor (+ a b) 2))
    (let ((y (* 2 x)))
      (+ x y))))

;; With positive divisor 3, ACL2 FLOOR represents the integer quotient used in
;; the source postcondition.

(defun verina-basic-99-int-div-by-three (result)
  (floor result 3))

(defun verina-basic-99-triple-postcond (x result)
  (and
   (integerp x)
   (integerp result)
   (let ((quotient
          (verina-basic-99-int-div-by-three result)))
     (and
      (equal quotient x)
      (equal (* quotient 3) result)))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Int domain, assumes exactly the source True precondition,
;; and applies the complete postcondition to the exact executable result.

(defun-sk verina-basic-99-triple-spec-satisfied-statement ()
  (forall (x)
    (implies
     (and
      (integerp x)
      (verina-basic-99-triple-precond x))
     (verina-basic-99-triple-postcond
      x
      (verina-basic-99-triple x)))))

(value-triple :itpeval-statement-checked)
:q
