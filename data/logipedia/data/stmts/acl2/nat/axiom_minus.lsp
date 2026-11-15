;; Statement-only formalization of Logipedia corpus artifact nat.axiom_minus,
;; catalog title "nat.axiom_minus": for every natural number, the natural
;; subtraction function is extensionally equal to its natural-filtered body.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued functions.

(defstub logipedia-nat-axiom-minus
  (left right)
  t)

(defstub logipedia-nat-axiom-minus-body
  (left right)
  t)

;; On natural indices, the source module's filter_nat_type is extensionally
;; the identity. This helper makes that definitional encoding explicit.
(defun logipedia-nat-axiom-minus-filtered-body (left right)
  (logipedia-nat-axiom-minus-body left right))

(defun-sk logipedia-nat-axiom-minus-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-minus left right)))))

(defun-sk logipedia-nat-axiom-minus-body-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-minus-body left right)))))

(defun-sk logipedia-nat-axiom-minus-pointwise-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-axiom-minus left right)
      (logipedia-nat-axiom-minus-filtered-body left right)))))

(defun logipedia-nat-axiom-minus-statement ()
  (implies
   (and
    (logipedia-nat-axiom-minus-typed-p)
    (logipedia-nat-axiom-minus-body-typed-p))
   (logipedia-nat-axiom-minus-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
