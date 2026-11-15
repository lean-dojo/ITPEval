;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.axiom_div_aux_body_O, catalog title
;; "div_mod.axiom_div_aux_body_O": at recursion index zero, the auxiliary
;; division body is extensionally the constant-zero function on two natural
;; arguments. This file contains no proof.

(in-package "ACL2")

;; ACL2 is first order, so equality of the source function values is represented
;; extensionally over their two natural arguments.
(defstub logipedia-div-mod-axiom-div-aux-body-o-raw
  (index dividend divisor)
  t)

(defun logipedia-div-mod-axiom-div-aux-body-o
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-axiom-div-aux-body-o-raw
    (nfix index)
    (nfix dividend)
    (nfix divisor))))

(defun-sk logipedia-div-mod-axiom-div-aux-body-o-statement ()
  (forall (dividend divisor)
    (implies
     (and
      (natp dividend)
      (natp divisor))
     (equal
      (logipedia-div-mod-axiom-div-aux-body-o
       0 dividend divisor)
      0))))

(value-triple :itpeval-statement-checked)
:q
