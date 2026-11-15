;; Statement-only formalization of Logipedia corpus artifact nat.axiom_eqb,
;; catalog title "nat.axiom_eqb": for every natural number, the Boolean
;; equality function is extensionally equal to its natural-filtered body.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's Boolean-valued functions.

(defstub logipedia-nat-axiom-eqb
  (left right)
  t)

(defstub logipedia-nat-axiom-eqb-body
  (left right)
  t)

;; On natural indices, the source module's filter_nat_type is extensionally
;; the identity. This helper makes that definitional encoding explicit.
(defun logipedia-nat-axiom-eqb-filtered-body (left right)
  (logipedia-nat-axiom-eqb-body left right))

(defun-sk logipedia-nat-axiom-eqb-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-axiom-eqb left right)))))

(defun-sk logipedia-nat-axiom-eqb-body-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-axiom-eqb-body left right)))))

(defun-sk logipedia-nat-axiom-eqb-pointwise-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-axiom-eqb left right)
      (logipedia-nat-axiom-eqb-filtered-body left right)))))

(defun logipedia-nat-axiom-eqb-statement ()
  (implies
   (and
    (logipedia-nat-axiom-eqb-typed-p)
    (logipedia-nat-axiom-eqb-body-typed-p))
   (logipedia-nat-axiom-eqb-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
