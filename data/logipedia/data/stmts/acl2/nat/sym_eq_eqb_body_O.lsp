;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_eqb_body_O, catalog title "nat.sym_eq_eqb_body_O": the function
;; that matches natural zero to true and every successor to false is
;; Leibniz-equal to the Boolean equality body at zero. This file contains no
;; proof.

(in-package "ACL2")

;; ACL2 has no first-class function values. Represent the fixed source
;; function eqb_body 0 by its application to a natural argument, then use
;; extensional equality as the target-native form of function equality.

(defstub logipedia-nat-sym-eq-eqb-body-o-eqb-body-o
  (m)
  t)

(defun logipedia-nat-sym-eq-eqb-body-o-match-value (m)
  (if (equal m 0)
      t
    nil))

(defun-sk logipedia-nat-sym-eq-eqb-body-o-statement ()
  (forall (m)
    (implies
     (natp m)
     (equal
      (logipedia-nat-sym-eq-eqb-body-o-match-value m)
      (logipedia-nat-sym-eq-eqb-body-o-eqb-body-o m)))))

(value-triple :itpeval-statement-checked)
:q
