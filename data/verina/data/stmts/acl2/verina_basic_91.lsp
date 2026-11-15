;; Statement-only formalization of VERINA corpus artifact verina_basic_91,
;; catalog title "Swap": a deterministic integer program exchanges its two
;; inputs and satisfies the complete swapped-pair contract. This file contains
;; no proof.

(in-package "ACL2")

;; The source precondition is True. The two Int input domains remain explicit
;; in the final correctness proposition.

(defun verina-basic-91-swap-precond (x y)
  (declare (ignore x y))
  t)

;; Lean Int x Int values are represented bijectively by ACL2 cons pairs whose
;; car and cdr range over all integers.

(defun verina-basic-91-int-pair-p (result)
  (and
   (consp result)
   (integerp (car result))
   (integerp (cdr result))))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. Alpha-renamed local bindings preserve the exact source
;; sequence: copy X and Y, save X in TMP, assign Y to X, and TMP to Y.

(defun verina-basic-91-swap (x y)
  (let* ((x-local x)
         (y-local y)
         (tmp x-local)
         (x-after-swap y-local)
         (y-after-swap tmp))
    (cons x-after-swap y-after-swap)))

;; This is the complete source postcondition: the pair components are Y and X,
;; and when the inputs differ each returned component differs from the input
;; originally occupying that position.

(defun verina-basic-91-swap-postcond (x y result)
  (and
   (integerp x)
   (integerp y)
   (verina-basic-91-int-pair-p result)
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

(defun-sk verina-basic-91-swap-spec-satisfied-statement ()
  (forall (x y)
    (implies
     (and
      (integerp x)
      (integerp y)
      (verina-basic-91-swap-precond x y))
     (verina-basic-91-swap-postcond
      x
      y
      (verina-basic-91-swap x y)))))

(value-triple :itpeval-statement-checked)
:q
