;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_times_body_O, catalog title "nat.axiom_times_body_O": the natural
;; multiplication body at zero is extensionally equal to the constant-zero
;; function on natural numbers. This file contains no proof.

(in-package "ACL2")

;; Conservative interface for the source's natural-valued binary function.

(defstub logipedia-nat-axiom-times-body-o
  (left right)
  t)

;; The source constant has type nat -> nat -> nat. In ACL2's untyped logic,
;; that ambient typing is an explicit interface hypothesis.

(defun-sk logipedia-nat-axiom-times-body-o-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (natp
      (logipedia-nat-axiom-times-body-o left right)))))

;; Equality at the source function type nat -> nat is rendered extensionally
;; over every natural argument.

(defun-sk logipedia-nat-axiom-times-body-o-pointwise-p ()
  (forall (m)
    (implies
     (natp m)
     (equal
      (logipedia-nat-axiom-times-body-o 0 m)
      0))))

(defun logipedia-nat-axiom-times-body-o-statement ()
  (implies
   (logipedia-nat-axiom-times-body-o-typed-p)
   (logipedia-nat-axiom-times-body-o-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
