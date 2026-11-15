;; Statement-only formalization of Logipedia corpus artifact bigops.timesAC,
;; catalog title "bigops.timesAC": the source's abstract ACop predicate holds
;; for natural numbers with neutral element one. This file contains no proof.

(in-package "ACL2")

;; ACop is opaque in every supplied source representation. This conservative
;; interface specializes its carrier parameter to the natural numbers.

(defstub logipedia-bigops-timesac-natural-acop-p (neutral-element) t)

(defun logipedia-bigops-timesac-statement ()
  (logipedia-bigops-timesac-natural-acop-p 1))

(value-triple :itpeval-statement-checked)
:q
