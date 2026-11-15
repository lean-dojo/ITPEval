;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.sym_eq_div_aux_body_O, catalog title
;; "div_mod.sym_eq_div_aux_body_O": at recursion index zero, the constant-zero
;; binary natural-number function is Leibniz-equal to the auxiliary division
;; body. This file contains no proof.

(in-package "ACL2")

;; ACL2 represents the source function
;; div_aux_body : nat -> nat -> nat -> nat by direct first-order application.

(defstub logipedia-div-mod-sym-eq-div-aux-body-o
  (index dividend divisor)
  t)

;; Universal equality on the complete natural-number input domain is the
;; first-order extensional rendering of the source function-level Leibniz
;; equality. The NATP guards below express source types, not hypotheses.

(defun-sk logipedia-div-mod-sym-eq-div-aux-body-o-statement ()
  (forall (dividend divisor)
    (implies
     (and
      (natp dividend)
      (natp divisor))
     (equal
      0
      (logipedia-div-mod-sym-eq-div-aux-body-o
       0 dividend divisor)))))

(value-triple :itpeval-statement-checked)
:q
