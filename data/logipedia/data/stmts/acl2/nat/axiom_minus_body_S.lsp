;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_minus_body_S, catalog title "nat.axiom_minus_body_S": at every
;; natural successor, the subtraction body returns S n at zero and returns
;; n minus q at an input S q. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-nat-axiom-minus-body-s-minus-raw
  (left right)
  t)

(defstub logipedia-nat-axiom-minus-body-s-raw
  (left right)
  t)

(defun logipedia-nat-axiom-minus-body-s-minus (left right)
  (nfix
   (logipedia-nat-axiom-minus-body-s-minus-raw
    (nfix left)
    (nfix right))))

(defun logipedia-nat-axiom-minus-body-s (left right)
  (nfix
   (logipedia-nat-axiom-minus-body-s-raw
    (nfix left)
    (nfix right))))

;; On ACL2 naturals, O is 0 and S is addition by one. This is the source
;; match_nat_type specialized to a successor-valued zero case and subtraction
;; at a successor argument.
(defun logipedia-nat-axiom-minus-body-s-successor-case (n m)
  (if (equal m 0)
      (+ n 1)
    (logipedia-nat-axiom-minus-body-s-minus n (- m 1))))

;; ACL2 is first order, so the source equality between unary function values is
;; represented extensionally over their natural argument.
(defun-sk logipedia-nat-axiom-minus-body-s-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (equal
      (logipedia-nat-axiom-minus-body-s (+ n 1) m)
      (logipedia-nat-axiom-minus-body-s-successor-case n m)))))

(value-triple :itpeval-statement-checked)
:q
