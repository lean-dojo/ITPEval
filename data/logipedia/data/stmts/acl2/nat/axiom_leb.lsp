;; Statement-only formalization of Logipedia corpus artifact nat.axiom_leb,
;; catalog title "nat.axiom_leb": for every natural number, the Boolean
;; less-than-or-equal function is extensionally equal to its natural-filtered
;; body. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's Boolean-valued functions.

(defstub logipedia-nat-axiom-leb
  (left right)
  t)

(defstub logipedia-nat-axiom-leb-body
  (left right)
  t)

;; On natural indices, the source module's filter_nat_type is extensionally
;; the identity. This helper makes that definitional encoding explicit.
(defun logipedia-nat-axiom-leb-filtered-body (left right)
  (logipedia-nat-axiom-leb-body left right))

(defun-sk logipedia-nat-axiom-leb-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-axiom-leb left right)))))

(defun-sk logipedia-nat-axiom-leb-body-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-axiom-leb-body left right)))))

(defun-sk logipedia-nat-axiom-leb-pointwise-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-axiom-leb left right)
      (logipedia-nat-axiom-leb-filtered-body left right)))))

(defun logipedia-nat-axiom-leb-statement ()
  (implies
   (and
    (logipedia-nat-axiom-leb-typed-p)
    (logipedia-nat-axiom-leb-body-typed-p))
   (logipedia-nat-axiom-leb-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
