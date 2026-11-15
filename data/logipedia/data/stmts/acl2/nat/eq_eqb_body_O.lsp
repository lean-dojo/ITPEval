;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_eqb_body_O, catalog title "nat.eq_eqb_body_O": the Boolean equality
;; body at natural zero is Leibniz-equal to the function that is true at zero
;; and false at every successor. This file contains no proof.

(in-package "ACL2")

;; On ACL2 naturals, this is the source match_nat_type with true at O and
;; the constant-false branch at S.
(defun logipedia-nat-eq-eqb-body-o-zero-case (m)
  (if (equal m 0)
      t
    nil))

;; The source eqb_body is a fixed opaque Boolean-valued binary function.
;; Booleanizing a conservative raw interface preserves that source type
;; without defining eqb_body O to be the requested right-hand side.
(defstub logipedia-nat-eq-eqb-body-o-raw
  (left right)
  t)

(defun logipedia-nat-eq-eqb-body-o-at-zero (m)
  (if
   (logipedia-nat-eq-eqb-body-o-raw 0 (nfix m))
   t
   nil))

;; Leibniz equality of the source functions nat -> bool is extensional
;; equality at every natural argument.
(defun-sk logipedia-nat-eq-eqb-body-o-statement ()
  (forall (m)
    (implies
     (natp m)
     (equal
      (logipedia-nat-eq-eqb-body-o-at-zero m)
      (logipedia-nat-eq-eqb-body-o-zero-case m)))))

(value-triple :itpeval-statement-checked)
:q
