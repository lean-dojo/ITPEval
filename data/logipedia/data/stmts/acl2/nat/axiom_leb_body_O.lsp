;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_leb_body_O, catalog title "nat.axiom_leb_body_O": the Boolean
;; less-than-or-equal body at natural zero is extensionally equal to the
;; constant-true function on natural numbers. This file contains no proof.

(in-package "ACL2")

;; Conservative interface for the source's natural-to-Boolean binary function.

(defstub logipedia-nat-axiom-leb-body-o
  (left right)
  t)

;; The source constant has type nat -> nat -> bool. In ACL2's untyped logic,
;; that ambient typing is an explicit interface hypothesis.

(defun-sk logipedia-nat-axiom-leb-body-o-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-axiom-leb-body-o left right)))))

;; Equality at the source function type nat -> bool is rendered extensionally
;; over every natural argument.

(defun-sk logipedia-nat-axiom-leb-body-o-pointwise-p ()
  (forall (m)
    (implies
     (natp m)
     (equal
      (logipedia-nat-axiom-leb-body-o 0 m)
      t))))

(defun logipedia-nat-axiom-leb-body-o-statement ()
  (implies
   (logipedia-nat-axiom-leb-body-o-typed-p)
   (logipedia-nat-axiom-leb-body-o-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
