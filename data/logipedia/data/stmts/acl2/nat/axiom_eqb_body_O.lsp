;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_eqb_body_O, catalog title "nat.axiom_eqb_body_O":
;; the Boolean equality body at natural zero is the function that is true
;; at zero and false at every successor. This file contains no proof.

(in-package "ACL2")

;; Conservative interface for the source's Boolean-valued binary function.

(defstub logipedia-nat-axiom-eqb-body-o
  (left right)
  t)

(defun logipedia-nat-axiom-eqb-body-o-zero-case (m)
  (if (equal m 0)
      t
    nil))

(defun-sk logipedia-nat-axiom-eqb-body-o-typed-p ()
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right))
     (booleanp
      (logipedia-nat-axiom-eqb-body-o left right)))))

(defun-sk logipedia-nat-axiom-eqb-body-o-pointwise-p ()
  (forall (m)
    (implies
     (natp m)
     (equal
      (logipedia-nat-axiom-eqb-body-o 0 m)
      (logipedia-nat-axiom-eqb-body-o-zero-case m)))))

(defun logipedia-nat-axiom-eqb-body-o-statement ()
  (implies
   (logipedia-nat-axiom-eqb-body-o-typed-p)
   (logipedia-nat-axiom-eqb-body-o-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
