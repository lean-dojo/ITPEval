;; Statement-only formalization of Logipedia corpus artifact nat.eq_leb,
;; catalog title "nat.eq_leb": for every natural number, the Boolean
;; less-than-or-equal function is Leibniz-equal to its natural-filtered body.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's Boolean-valued functions.

(defstub logipedia-nat-eq-leb
  (left right)
  t)

(defstub logipedia-nat-eq-leb-body
  (left right)
  t)

;; The source module's filter_nat_type is extensionally the identity on
;; natural indices. Function-valued Leibniz equality is represented by
;; equality at every natural argument.
(defun logipedia-nat-eq-leb-filtered-body (left right)
  (logipedia-nat-eq-leb-body left right))

(defun-sk logipedia-nat-eq-leb-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-eq-leb left right)))))

(defun-sk logipedia-nat-eq-leb-body-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-eq-leb-body left right)))))

(defun-sk logipedia-nat-eq-leb-pointwise-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-eq-leb left right)
      (logipedia-nat-eq-leb-filtered-body left right)))))

(defun logipedia-nat-eq-leb-statement ()
  (implies
   (and
    (logipedia-nat-eq-leb-typed-p)
    (logipedia-nat-eq-leb-body-typed-p))
   (logipedia-nat-eq-leb-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
