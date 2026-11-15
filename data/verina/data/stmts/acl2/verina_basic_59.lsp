;; Statement-only formalization of VERINA corpus artifact verina_basic_59,
;; catalog title "DoubleQuadruple": a deterministic integer program returns
;; a pair whose first component is twice the input and whose second component
;; is twice the first component. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Int input domain remains explicit in
;; the final correctness proposition.

(defun verina-basic-59-double-quadruple-precond (x)
  (declare (ignore x))
  t)

;; Lean Int x Int values are represented bijectively by ACL2 cons pairs whose
;; car and cdr range over all integers.

(defun verina-basic-59-int-pair-p (result)
  (and
   (consp result)
   (integerp (car result))
   (integerp (cdr result))))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The two lets preserve the exact source computation: first
;; A is twice X, then B is twice A.

(defun verina-basic-59-double-quadruple (x)
  (let* ((a (* 2 x))
         (b (* 2 a)))
    (cons a b)))

;; This is the complete source postcondition. The result is a typed integer
;; pair, its first component is twice X, and its second is twice its first.

(defun verina-basic-59-double-quadruple-postcond
    (x result)
  (and
   (integerp x)
   (verina-basic-59-int-pair-p result)
   (equal (car result) (* 2 x))
   (equal (cdr result) (* 2 (car result)))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every integer input, assumes exactly the source True precondition, and
;; applies the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-59-double-quadruple-spec-satisfied-statement
    ()
  (forall (x)
    (implies
     (and
      (integerp x)
      (verina-basic-59-double-quadruple-precond x))
     (verina-basic-59-double-quadruple-postcond
      x
      (verina-basic-59-double-quadruple x)))))

(value-triple :itpeval-statement-checked)
:q
