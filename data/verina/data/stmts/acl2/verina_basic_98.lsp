;; Statement-only formalization of VERINA corpus artifact verina_basic_98,
;; catalog title "Triple": a deterministic integer program returns three times
;; its input and satisfies the source quotient-and-divisibility contract. This
;; file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Int binder domain remains explicit in
;; the final correctness proposition.

(defun verina-basic-98-triple-precond (x)
  (declare (ignore x))
  t)

;; The proof-valued precondition argument has no computational effect and is
;; erased. This is the exact source implementation x * 3.

(defun verina-basic-98-triple (x)
  (* x 3))

;; With positive divisor 3, ACL2 FLOOR represents the integer quotient used in
;; the source postcondition.

(defun verina-basic-98-int-div-by-three (result)
  (floor result 3))

(defun verina-basic-98-triple-postcond (x result)
  (and
   (integerp x)
   (integerp result)
   (let ((quotient
          (verina-basic-98-int-div-by-three result)))
     (and
      (equal quotient x)
      (equal (* quotient 3) result)))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Int domain, assumes exactly the source True precondition,
;; and applies the complete postcondition to the exact executable result.

(defun-sk verina-basic-98-triple-spec-satisfied-statement ()
  (forall (x)
    (implies
     (and
      (integerp x)
      (verina-basic-98-triple-precond x))
     (verina-basic-98-triple-postcond
      x
      (verina-basic-98-triple x)))))

(value-triple :itpeval-statement-checked)
:q
