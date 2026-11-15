;; Statement-only formalization of Logipedia corpus artifact nat.axiom_times,
;; catalog title "nat.axiom_times": for every natural number, the natural
;; multiplication function is extensionally equal to its natural-filtered
;; body. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's natural-valued functions.

(defstub logipedia-nat-axiom-times
  (left right)
  t)

(defstub logipedia-nat-axiom-times-body
  (left right)
  t)

;; On natural indices, the source module's filter_nat_type is extensionally
;; the identity. This helper makes that definitional encoding explicit.
(defun logipedia-nat-axiom-times-filtered-body (left right)
  (logipedia-nat-axiom-times-body left right))

(defun-sk logipedia-nat-axiom-times-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-times left right)))))

(defun-sk logipedia-nat-axiom-times-body-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-times-body left right)))))

(defun-sk logipedia-nat-axiom-times-pointwise-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (equal
      (logipedia-nat-axiom-times left right)
      (logipedia-nat-axiom-times-filtered-body left right)))))

(defun logipedia-nat-axiom-times-statement ()
  (implies
   (and
    (logipedia-nat-axiom-times-typed-p)
    (logipedia-nat-axiom-times-body-typed-p))
   (logipedia-nat-axiom-times-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
