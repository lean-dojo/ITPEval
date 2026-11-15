;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.eq_div_aux_body_O, catalog title "div_mod.eq_div_aux_body_O":
;; at recursion index zero, the auxiliary division body is extensionally equal
;; to the constant-zero function on two natural arguments. This file contains
;; no proof.

(in-package "ACL2")

;; Conservative interface for the source function
;; div_aux_body : nat -> nat -> nat -> nat.
(defstub logipedia-div-mod-div-aux-body (index dividend divisor) t)

;; Pointwise equality on the complete natural-number domain is the
;; target-native extensional rendering of the source binary-function equality.
(defun-sk logipedia-div-mod-eq-div-aux-body-o-statement ()
  (forall (dividend divisor)
    (implies
     (and (natp dividend)
          (natp divisor))
     (equal
      (logipedia-div-mod-div-aux-body 0 dividend divisor)
      0))))

(value-triple :itpeval-statement-checked)
:q
