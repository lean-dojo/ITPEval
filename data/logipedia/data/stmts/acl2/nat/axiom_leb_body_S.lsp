;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_leb_body_S, catalog title "nat.axiom_leb_body_S": for every
;; natural number, the Boolean less-than-or-equal body at its successor is
;; extensionally equal to the function that is false at zero and applies
;; less-than-or-equal to the predecessor at a successor. This file contains
;; no proof.

(in-package "ACL2")

;; Conservative interfaces for the source's Boolean-valued functions.

(defstub logipedia-nat-axiom-leb-body-s-leb
  (left right)
  t)

(defstub logipedia-nat-axiom-leb-body-s
  (left right)
  t)

;; On ACL2 naturals, O is 0 and S is addition by one. This is the source
;; match_nat_type specialized to a Boolean zero case and a LEB successor
;; case.
(defun logipedia-nat-axiom-leb-body-s-successor-case (n m)
  (if (equal m 0)
      nil
    (logipedia-nat-axiom-leb-body-s-leb n (- m 1))))

(defun-sk logipedia-nat-axiom-leb-body-s-leb-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-axiom-leb-body-s-leb left right)))))

(defun-sk logipedia-nat-axiom-leb-body-s-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-axiom-leb-body-s left right)))))

;; Equality at the source function type nat -> bool is rendered extensionally
;; over every natural argument.
(defun-sk logipedia-nat-axiom-leb-body-s-pointwise-p ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (equal
      (logipedia-nat-axiom-leb-body-s (+ n 1) m)
      (logipedia-nat-axiom-leb-body-s-successor-case n m)))))

(defun logipedia-nat-axiom-leb-body-s-statement ()
  (implies
   (and
    (logipedia-nat-axiom-leb-body-s-leb-typed-p)
    (logipedia-nat-axiom-leb-body-s-typed-p))
   (logipedia-nat-axiom-leb-body-s-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
