;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_plus_body_O, catalog title "nat.axiom_plus_body_O": the natural
;; addition body at zero is extensionally equal to the identity function on
;; natural numbers. This file contains no proof.

(in-package "ACL2")

;; Conservative interface for the source's natural-valued binary function.

(defstub logipedia-nat-axiom-plus-body-o
  (left right)
  t)

(defun-sk logipedia-nat-axiom-plus-body-o-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-plus-body-o left right)))))

(defun-sk logipedia-nat-axiom-plus-body-o-pointwise-p ()
  (forall (m)
    (implies
     (natp m)
     (equal
      (logipedia-nat-axiom-plus-body-o 0 m)
      m))))

(defun logipedia-nat-axiom-plus-body-o-statement ()
  (and
   (logipedia-nat-axiom-plus-body-o-typed-p)
   (logipedia-nat-axiom-plus-body-o-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
