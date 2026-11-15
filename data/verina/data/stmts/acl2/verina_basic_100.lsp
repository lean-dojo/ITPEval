;; Statement-only formalization of VERINA corpus artifact verina_basic_100,
;; "Triple": a deterministic integer program returns three times its input,
;; with the source quotient-and-divisibility postcondition. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Int binder domain remains explicit in
;; the final correctness statement.

(defun verina-basic-100-triple-precond (x)
  (declare (ignore x))
  t)

;; The proof-valued precondition argument has no computational effect and is
;; erased. This preserves the source branch, local binding, and integer
;; arithmetic exactly.

(defun verina-basic-100-triple (x)
  (if (equal x 0)
      0
    (let ((y (* 2 x)))
      (+ x y))))

;; With positive divisor 3, ACL2 FLOOR is Lean Int division: the Euclidean
;; quotient whose remainder is nonnegative and less than 3.

(defun verina-basic-100-int-div-by-three (result)
  (floor result 3))

(defun verina-basic-100-triple-postcond (x result)
  (and
   (integerp x)
   (integerp result)
   (let ((quotient
          (verina-basic-100-int-div-by-three result)))
     (and
      (equal quotient x)
      (equal (* quotient 3) result)))))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Int input and True precondition, and applies the complete
;; postcondition to the exact executable result.

(defun verina-basic-100-triple-spec-satisfied-statement (x)
  (implies
   (and
    (integerp x)
    (verina-basic-100-triple-precond x))
   (verina-basic-100-triple-postcond
    x
    (verina-basic-100-triple x))))

(value-triple :itpeval-statement-checked)
:q
