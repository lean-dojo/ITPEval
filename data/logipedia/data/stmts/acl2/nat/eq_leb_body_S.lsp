;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_leb_body_S, catalog title "nat.eq_leb_body_S": for every natural
;; number, the Boolean less-than-or-equal body at its successor is
;; Leibniz-equal to the function that is false at zero and applies
;; less-than-or-equal to the predecessors at a successor. This file contains
;; no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's Boolean-valued functions.

(defstub logipedia-nat-eq-leb-body-s-leb
  (left right)
  t)

(defstub logipedia-nat-eq-leb-body-s
  (left right)
  t)

;; On ACL2 naturals, O is 0 and S is addition by one. This is the source
;; match_nat_type specialized to a Boolean zero case and a LEB successor
;; case.
(defun logipedia-nat-eq-leb-body-s-successor-case (n m)
  (if (equal m 0)
      nil
    (logipedia-nat-eq-leb-body-s-leb n (- m 1))))

(defun-sk logipedia-nat-eq-leb-body-s-leb-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-eq-leb-body-s-leb left right)))))

(defun-sk logipedia-nat-eq-leb-body-s-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-eq-leb-body-s left right)))))

;; Leibniz equality of the source functions nat -> bool is extensional
;; equality at every natural argument.
(defun-sk logipedia-nat-eq-leb-body-s-pointwise-p ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (equal
      (logipedia-nat-eq-leb-body-s (+ n 1) m)
      (logipedia-nat-eq-leb-body-s-successor-case n m)))))

(defun logipedia-nat-eq-leb-body-s-statement ()
  (implies
   (and
    (logipedia-nat-eq-leb-body-s-leb-typed-p)
    (logipedia-nat-eq-leb-body-s-typed-p))
   (logipedia-nat-eq-leb-body-s-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
