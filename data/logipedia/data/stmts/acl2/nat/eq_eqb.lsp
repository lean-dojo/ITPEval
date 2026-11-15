;; Statement-only formalization of Logipedia corpus artifact nat.eq_eqb,
;; catalog title "nat.eq_eqb": for every natural number, the Boolean
;; equality function is Leibniz-equal to its natural-filtered body.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces under Boolean wrappers represent the source
;; functions without adding typing hypotheses to the proposition.

(defstub logipedia-nat-eq-eqb-raw
  (left right)
  t)

(defstub logipedia-nat-eq-eqb-body-raw
  (left right)
  t)

(defun logipedia-nat-eq-eqb (left right)
  (if (logipedia-nat-eq-eqb-raw left right)
      t
    nil))

(defun logipedia-nat-eq-eqb-body (left right)
  (if (logipedia-nat-eq-eqb-body-raw left right)
      t
    nil))

;; The source module's filter_nat_type is extensionally the identity on
;; natural indices. Function-valued Leibniz equality is represented by
;; equality at every natural argument.
(defun logipedia-nat-eq-eqb-filtered-body (left right)
  (logipedia-nat-eq-eqb-body left right))

(defun-sk logipedia-nat-eq-eqb-statement ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-eq-eqb left right)
      (logipedia-nat-eq-eqb-filtered-body left right)))))

(value-triple :itpeval-statement-checked)
:q
