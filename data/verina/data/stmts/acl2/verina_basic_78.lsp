;; Statement-only formalization of VERINA corpus artifact verina_basic_78,
;; catalog title "MultipleReturns": a deterministic integer program returns
;; the pair consisting of the sum and difference of its two inputs. This file
;; contains no proof.

(in-package "ACL2")

;; The source precondition is True. The two Int input domains remain explicit
;; in the final correctness proposition.

(defun verina-basic-78-multiple-returns-precond (x y)
  (declare (ignore x y))
  t)

;; Lean Int x Int values are represented bijectively by ACL2 cons pairs whose
;; car and cdr range over all integers.

(defun verina-basic-78-int-pair-p (result)
  (and
   (consp result)
   (integerp (car result))
   (integerp (cdr result))))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The two LET bindings and returned pair preserve the complete
;; source implementation.

(defun verina-basic-78-multiple-returns (x y)
  (let* ((more (+ x y))
         (less (- x y)))
    (cons more less)))

;; This is the complete source postcondition. The pair is integer-valued, its
;; first component is x + y, and its second component plus y equals x.

(defun verina-basic-78-multiple-returns-postcond
    (x y result)
  (and
   (integerp x)
   (integerp y)
   (verina-basic-78-int-pair-p result)
   (equal (car result) (+ x y))
   (equal (+ (cdr result) y) x)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every pair of integer inputs, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact executable
;; result.

(defun-sk
    verina-basic-78-multiple-returns-spec-satisfied-statement
    ()
  (forall (x y)
    (implies
     (and
      (integerp x)
      (integerp y)
      (verina-basic-78-multiple-returns-precond x y))
     (verina-basic-78-multiple-returns-postcond
      x
      y
      (verina-basic-78-multiple-returns x y)))))

(value-triple :itpeval-statement-checked)
:q
