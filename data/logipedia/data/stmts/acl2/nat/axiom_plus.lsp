;; Statement-only formalization of Logipedia corpus artifact nat.axiom_plus,
;; catalog title "nat.axiom_plus": for every natural number, the natural
;; addition function is extensionally equal to its natural-filtered body.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued functions.

(defstub logipedia-nat-axiom-plus
  (left right)
  t)

(defstub logipedia-nat-axiom-plus-body
  (left right)
  t)

;; On natural indices, the source module's filter_nat_type is extensionally
;; the identity. This helper makes that definitional encoding explicit.
(defun logipedia-nat-axiom-plus-filtered-body (left right)
  (logipedia-nat-axiom-plus-body left right))

(defun-sk logipedia-nat-axiom-plus-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-plus left right)))))

(defun-sk logipedia-nat-axiom-plus-body-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-plus-body left right)))))

(defun-sk logipedia-nat-axiom-plus-pointwise-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-axiom-plus left right)
      (logipedia-nat-axiom-plus-filtered-body left right)))))

(defun logipedia-nat-axiom-plus-statement ()
  (implies
   (and
    (logipedia-nat-axiom-plus-typed-p)
    (logipedia-nat-axiom-plus-body-typed-p))
   (logipedia-nat-axiom-plus-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
