;; Statement-only formalization of PutnamBench corpus artifact putnam_1977_b5:
;; a strict quadratic-sum bound for n real numbers implies that A is less
;; than twice every pairwise product. This file contains no proof.

(in-package "ACL2")

;; A length-n list is definitionally equivalent to a function on Fin n, with
;; list order corresponding to the index order. Standard ACL2 represents the
;; entries by exact rationals. This is bidirectionally equivalent to validity
;; over the reals. One direction is immediate. Conversely, a real
;; counterexample has positive slack in the strict sum hypothesis. If its
;; failed pairwise conclusion is an equality, increasing A by less than that
;; slack makes the failure strict while preserving the hypothesis. Continuity
;; then gives a neighborhood of counterexamples, and density supplies rational
;; values in that neighborhood.
;;
;; The strict sum hypothesis is essential and agrees with the Lean, Isabelle,
;; and stated Putnam formulation. Replacing it by a non-strict inequality, as
;; in the Rocq spelling, admits n=2, values=(1 1), A=2 as a counterexample.

(defun putnam-1977-b5-rational-list-p (values)
  (if (consp values)
      (and (rationalp (car values))
           (putnam-1977-b5-rational-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1977-b5-sum (values)
  (if (consp values)
      (+ (car values)
         (putnam-1977-b5-sum (cdr values)))
    0))

(defun putnam-1977-b5-sum-squares (values)
  (if (consp values)
      (+ (* (car values) (car values))
         (putnam-1977-b5-sum-squares (cdr values)))
    0))

(defun putnam-1977-b5-bound-against-rest-p
    (first rest a)
  (if (consp rest)
      (and (< a (* 2 first (car rest)))
           (putnam-1977-b5-bound-against-rest-p
            first (cdr rest) a))
    t))

(defun putnam-1977-b5-all-pairs-p (values a)
  (if (consp values)
      (and (putnam-1977-b5-bound-against-rest-p
            (car values) (cdr values) a)
           (putnam-1977-b5-all-pairs-p (cdr values) a))
    t))

(defun putnambench-putnam-1977-b5-statement
    (n values a)
  (implies
   (and (natp n)
        (< 1 n)
        (true-listp values)
        (equal (len values) n)
        (putnam-1977-b5-rational-list-p values)
        (rationalp a)
        (< (+ a
              (putnam-1977-b5-sum-squares values))
           (* (/ 1 (- n 1))
              (expt (putnam-1977-b5-sum values) 2))))
   (putnam-1977-b5-all-pairs-p values a)))

(value-triple :itpeval-statement-checked)
:q
