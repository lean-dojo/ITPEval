;; Statement-only formalization of Logipedia corpus artifact bigops.timesA,
;; catalog title "bigops.timesA": the source's abstract Aop predicate holds
;; for natural numbers with neutral element one. This file contains no proof.

(in-package "ACL2")

;; Aop is opaque in every supplied source representation. This conservative
;; interface specializes its carrier parameter to the natural numbers.

(defstub logipedia-bigops-timesa-natural-aop-p (neutral-element) t)

(defun logipedia-bigops-timesa-statement ()
  (logipedia-bigops-timesa-natural-aop-p 1))

(value-triple :itpeval-statement-checked)
:q
