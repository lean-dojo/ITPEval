;; Statement-only formalization of Logipedia corpus artifact nat.sym_eq_leb,
;; catalog title "nat.sym_eq_leb": for every natural number, the
;; natural-filtered Boolean less-than-or-equal body is Leibniz-equal to the
;; Boolean less-than-or-equal function. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's Boolean-valued functions.

(defstub logipedia-nat-sym-eq-leb
  (left right)
  t)

(defstub logipedia-nat-sym-eq-leb-body
  (left right)
  t)

;; The source module's filter_nat_type is extensionally the identity on
;; natural indices. Function-valued Leibniz equality is represented by
;; equality at every natural argument.
(defun logipedia-nat-sym-eq-leb-filtered-body (left right)
  (logipedia-nat-sym-eq-leb-body left right))

(defun-sk logipedia-nat-sym-eq-leb-statement ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-sym-eq-leb-filtered-body left right)
      (logipedia-nat-sym-eq-leb left right)))))

(value-triple :itpeval-statement-checked)
:q
