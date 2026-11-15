;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.axiom_mod_aux_body_O, catalog title
;; "div_mod.axiom_mod_aux_body_O": at recursion index zero, the auxiliary
;; remainder body is extensionally the binary natural-number function that
;; returns its first argument. This file contains no proof.

(in-package "ACL2")

;; ACL2 is first order, so equality of the source function values is represented
;; extensionally over their two natural arguments.
(defstub logipedia-div-mod-axiom-mod-aux-body-o-raw
  (index dividend divisor)
  t)

(defun logipedia-div-mod-axiom-mod-aux-body-o
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-axiom-mod-aux-body-o-raw
    (nfix index)
    (nfix dividend)
    (nfix divisor))))

(defun-sk logipedia-div-mod-axiom-mod-aux-body-o-statement ()
  (forall (dividend divisor)
    (implies
     (and
      (natp dividend)
      (natp divisor))
     (equal
      (logipedia-div-mod-axiom-mod-aux-body-o
       0 dividend divisor)
      dividend))))

(value-triple :itpeval-statement-checked)
:q
