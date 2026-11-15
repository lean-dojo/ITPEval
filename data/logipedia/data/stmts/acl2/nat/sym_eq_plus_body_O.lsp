;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_plus_body_O, catalog title "nat.sym_eq_plus_body_O": the
;; identity function on natural numbers is Leibniz-equal to the natural
;; addition body at zero. This file contains no proof.

(in-package "ACL2")

;; ACL2 has no first-class function values, so the fixed source function
;; plus_body : nat -> nat -> nat is represented by one fixed binary stub.
;; NFIX gives that stub the source's natural codomain without adding a
;; hypothesis that could make the proposition vacuous.

(defstub logipedia-nat-sym-eq-plus-body-o-raw
  (left right)
  t)

(defun logipedia-nat-sym-eq-plus-body-o (left right)
  (nfix
   (logipedia-nat-sym-eq-plus-body-o-raw
    (nfix left)
    (nfix right))))

;; Function-valued Leibniz equality is represented extensionally at every
;; natural argument, in the source direction identity = plus_body 0.
(defun-sk logipedia-nat-sym-eq-plus-body-o-statement ()
  (forall (m)
    (implies
     (natp m)
     (equal
      m
      (logipedia-nat-sym-eq-plus-body-o 0 m)))))

(value-triple :itpeval-statement-checked)
:q
