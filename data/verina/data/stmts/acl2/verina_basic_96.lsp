;; Statement-only formalization of VERINA corpus artifact verina_basic_96,
;; catalog title "SwapSimultaneous": a deterministic integer program returns
;; the ordered pair formed by swapping its two inputs and satisfies the full
;; swapped-pair contract. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The two Int input domains remain explicit
;; in the final correctness proposition.

(defun verina-basic-96-swap-simultaneous-precond (x y)
  (declare (ignore x y))
  t)

;; Lean Int x Int values are represented bijectively by ACL2 cons pairs whose
;; car and cdr range over all integers.

(defun verina-basic-96-int-pair-p (result)
  (and
   (consp result)
   (integerp (car result))
   (integerp (cdr result))))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. Returning (Y, X) preserves the complete source computation.

(defun verina-basic-96-swap-simultaneous (x y)
  (cons y x))

;; This is the complete source postcondition, including the implication that
;; both output components differ from their original positions when X and Y
;; differ.

(defun verina-basic-96-swap-simultaneous-postcond
    (x y result)
  (and
   (integerp x)
   (integerp y)
   (verina-basic-96-int-pair-p result)
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
;; result.

(defun-sk
    verina-basic-96-swap-simultaneous-spec-satisfied-statement
    ()
  (forall (x y)
    (implies
     (and
      (integerp x)
      (integerp y)
      (verina-basic-96-swap-simultaneous-precond
       x
       y))
     (verina-basic-96-swap-simultaneous-postcond
      x
      y
      (verina-basic-96-swap-simultaneous
       x
       y)))))

(value-triple :itpeval-statement-checked)
:q
