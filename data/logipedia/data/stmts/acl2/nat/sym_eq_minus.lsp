;; Statement-only formalization of Logipedia corpus artifact nat.sym_eq_minus,
;; catalog title "nat.sym_eq_minus": for every natural number, the
;; natural-filtered subtraction body is Leibniz-equal to the natural
;; subtraction function. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued functions.

(defstub logipedia-nat-sym-eq-minus
  (left right)
  t)

(defstub logipedia-nat-sym-eq-minus-body
  (left right)
  t)

;; The source module's filter_nat_type is extensionally the identity on
;; natural indices. Function-valued Leibniz equality is represented by
;; equality at every natural argument.
(defun logipedia-nat-sym-eq-minus-filtered-body (left right)
  (logipedia-nat-sym-eq-minus-body left right))

(defun-sk logipedia-nat-sym-eq-minus-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-sym-eq-minus left right)))))

(defun-sk logipedia-nat-sym-eq-minus-body-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-sym-eq-minus-body left right)))))

(defun-sk logipedia-nat-sym-eq-minus-pointwise-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-sym-eq-minus-filtered-body left right)
      (logipedia-nat-sym-eq-minus left right)))))

(defun logipedia-nat-sym-eq-minus-statement ()
  (implies
   (and
    (logipedia-nat-sym-eq-minus-typed-p)
    (logipedia-nat-sym-eq-minus-body-typed-p))
   (logipedia-nat-sym-eq-minus-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
