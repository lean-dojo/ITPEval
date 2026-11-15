;; Statement-only formalization of Logipedia corpus artifact
;; div_mod.axiom_div_aux, catalog title "div_mod.axiom_div_aux": for every
;; natural recursion index, the auxiliary division function is extensionally
;; equal to its natural-filtered body. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-div-mod-axiom-div-aux-raw
  (index dividend divisor)
  t)

(defstub logipedia-div-mod-axiom-div-aux-body-raw
  (index dividend divisor)
  t)

(defun logipedia-div-mod-axiom-div-aux
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-axiom-div-aux-raw
    (nfix index)
    (nfix dividend)
    (nfix divisor))))

(defun logipedia-div-mod-axiom-div-aux-body
    (index dividend divisor)
  (nfix
   (logipedia-div-mod-axiom-div-aux-body-raw
    (nfix index)
    (nfix dividend)
    (nfix divisor))))

;; ACL2 is first order, so equality of the source function values is represented
;; extensionally. At a natural index, filter_nat_type returns the body at that
;; same index.
(defun-sk logipedia-div-mod-axiom-div-aux-statement ()
  (forall (index dividend divisor)
    (implies
     (and
      (natp index)
      (natp dividend)
      (natp divisor))
     (equal
      (logipedia-div-mod-axiom-div-aux
       index dividend divisor)
      (logipedia-div-mod-axiom-div-aux-body
       index dividend divisor)))))

(value-triple :itpeval-statement-checked)
:q
