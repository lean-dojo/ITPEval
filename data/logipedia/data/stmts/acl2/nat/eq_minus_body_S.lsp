;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_minus_body_S, catalog title "nat.eq_minus_body_S": for every natural
;; number, the subtraction body at its successor is Leibniz-equal to the
;; function that returns that successor at zero and subtracts the predecessor
;; from the number at successor inputs. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued functions.

(defstub logipedia-nat-eq-minus-body-s-minus
  (left right)
  t)

(defstub logipedia-nat-eq-minus-body-s
  (left right)
  t)

;; On ACL2 naturals, O is 0 and S is addition by one. This is the source
;; match_nat_type specialized to its natural-valued zero and successor cases.
(defun logipedia-nat-eq-minus-body-s-successor-case (n m)
  (if (equal m 0)
      (+ n 1)
    (logipedia-nat-eq-minus-body-s-minus n (- m 1))))

(defun-sk logipedia-nat-eq-minus-body-s-minus-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-eq-minus-body-s-minus left right)))))

(defun-sk logipedia-nat-eq-minus-body-s-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-eq-minus-body-s left right)))))

;; Leibniz equality of the source functions nat -> nat is extensional equality
;; at every natural argument.
(defun-sk logipedia-nat-eq-minus-body-s-pointwise-p ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (equal
      (logipedia-nat-eq-minus-body-s (+ n 1) m)
      (logipedia-nat-eq-minus-body-s-successor-case n m)))))

(defun logipedia-nat-eq-minus-body-s-statement ()
  (implies
   (and
    (logipedia-nat-eq-minus-body-s-minus-typed-p)
    (logipedia-nat-eq-minus-body-s-typed-p))
   (logipedia-nat-eq-minus-body-s-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
