;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_eqb_body_S, catalog title "nat.eq_eqb_body_S": for every natural
;; number, the Boolean equality body at its successor is Leibniz-equal to the
;; function that is false at zero and applies equality to both predecessors
;; at a successor. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's Boolean-valued functions.

(defstub logipedia-nat-eq-eqb-body-s-eqb
  (left right)
  t)

(defstub logipedia-nat-eq-eqb-body-s
  (left right)
  t)

;; On ACL2 naturals, O is 0 and S is addition by one. This is the source
;; match_nat_type specialized to a Boolean zero case and an EQB successor
;; case.
(defun logipedia-nat-eq-eqb-body-s-successor-case (n m)
  (if (equal m 0)
      nil
    (logipedia-nat-eq-eqb-body-s-eqb n (- m 1))))

(defun-sk logipedia-nat-eq-eqb-body-s-eqb-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-eq-eqb-body-s-eqb left right)))))

(defun-sk logipedia-nat-eq-eqb-body-s-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-eq-eqb-body-s left right)))))

;; Leibniz equality of the source functions nat -> bool is extensional
;; equality at every natural argument.
(defun-sk logipedia-nat-eq-eqb-body-s-pointwise-p ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (equal
      (logipedia-nat-eq-eqb-body-s (+ n 1) m)
      (logipedia-nat-eq-eqb-body-s-successor-case n m)))))

(defun logipedia-nat-eq-eqb-body-s-statement ()
  (implies
   (and
    (logipedia-nat-eq-eqb-body-s-eqb-typed-p)
    (logipedia-nat-eq-eqb-body-s-typed-p))
   (logipedia-nat-eq-eqb-body-s-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
