;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_minus_body_O, catalog title "nat.axiom_minus_body_O": the natural
;; subtraction body at zero is extensionally equal to the constant-zero
;; function on natural numbers. This file contains no proof.

(in-package "ACL2")

;; Conservative interface for the source natural-valued binary function.
(defstub logipedia-nat-axiom-minus-body-o (left right) t)

(defun-sk logipedia-nat-axiom-minus-body-o-typed-p ()
  (forall (left right)
    (implies (and (natp left)
                  (natp right))
             (natp (logipedia-nat-axiom-minus-body-o left right)))))

(defun-sk logipedia-nat-axiom-minus-body-o-pointwise-p ()
  (forall (m)
    (implies (natp m)
             (equal (logipedia-nat-axiom-minus-body-o 0 m)
                    0))))

(defun logipedia-nat-axiom-minus-body-o-statement ()
  (and (logipedia-nat-axiom-minus-body-o-typed-p)
       (logipedia-nat-axiom-minus-body-o-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
