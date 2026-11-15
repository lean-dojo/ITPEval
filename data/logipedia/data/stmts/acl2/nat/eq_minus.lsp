;; Statement-only formalization of Logipedia corpus artifact nat.eq_minus,
;; catalog title "nat.eq_minus": for every natural number, the natural
;; subtraction function is Leibniz-equal to its natural-filtered body.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued functions.

(defstub logipedia-nat-eq-minus
  (left right)
  t)

(defstub logipedia-nat-eq-minus-body
  (left right)
  t)

;; The source module's filter_nat_type is extensionally the identity on
;; natural indices. Function-valued Leibniz equality is represented by
;; equality at every natural argument.
(defun logipedia-nat-eq-minus-filtered-body (left right)
  (logipedia-nat-eq-minus-body left right))

(defun-sk logipedia-nat-eq-minus-pointwise-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-eq-minus left right)
      (logipedia-nat-eq-minus-filtered-body left right)))))

(defun logipedia-nat-eq-minus-statement ()
  (logipedia-nat-eq-minus-pointwise-p))

(value-triple :itpeval-statement-checked)
:q
