;; Statement-only formalization of VERINA corpus artifact verina_basic_92,
;; catalog title "SwapArithmetic": a deterministic integer arithmetic program
;; exchanges its two inputs and satisfies the complete swapped-pair contract.
;; This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The two Int input domains remain explicit
;; in the final correctness proposition.

(defun verina-basic-92-swap-arithmetic-precond (x y)
  (declare (ignore x y))
  t)

;; Lean Int x Int values are represented bijectively by ACL2 cons pairs whose
;; car and cdr range over all integers.

(defun verina-basic-92-int-pair-p (result)
  (and
   (consp result)
   (integerp (car result))
   (integerp (cdr result))))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The LET* bindings preserve the exact source arithmetic
;; sequence.

(defun verina-basic-92-swap-arithmetic (x y)
  (let* ((x1 x)
         (y1 y)
         (x2 (- y1 x1))
         (y2 (- y1 x2))
         (x3 (+ y2 x2)))
    (cons x3 y2)))

;; This is the complete source postcondition: the pair components are Y and X,
;; and when the inputs differ each returned component differs from the input
;; originally occupying that position.

(defun verina-basic-92-swap-arithmetic-postcond
    (x y result)
  (and
   (integerp x)
   (integerp y)
   (verina-basic-92-int-pair-p result)
   (equal (car result) y)
   (equal (cdr result) x)
   (implies
    (not (equal x y))
    (and
     (not (equal (car result) x))
     (not (equal (cdr result) y))))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every pair of integer inputs, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact executable
;; arithmetic result.

(defun-sk
    verina-basic-92-swap-arithmetic-spec-satisfied-statement
    ()
  (forall (x y)
    (implies
     (and
      (integerp x)
      (integerp y)
      (verina-basic-92-swap-arithmetic-precond
       x
       y))
     (verina-basic-92-swap-arithmetic-postcond
      x
      y
      (verina-basic-92-swap-arithmetic
       x
       y)))))

(value-triple :itpeval-statement-checked)
:q
