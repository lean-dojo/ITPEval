;; Statement-only formalization of Logipedia corpus artifact
;; bigops.bigop_false, catalog title "bigops.bigop_false": a polymorphic
;; big operation selected by the constantly false Boolean predicate returns
;; its neutral-element argument at every natural bound.
;; This file contains no proof.

(in-package "ACL2")

;; The constantly false selector has empty support, so the source bigop never
;; observes the operation or sequence.  They remain arbitrary, universally
;; quantified parameters, while each recursive step returns the prior fold.

(defun logipedia-bigops-false-bigop
    (index nil-value operation sequence)
  (declare
   (ignore operation sequence)
   (xargs :measure (nfix index)))
  (if (zp index)
      nil-value
    (logipedia-bigops-false-bigop
     (- index 1)
     nil-value
     nil
     nil)))

(defun-sk logipedia-bigops-bigop-false-statement ()
  (forall (n nil-value operation sequence)
    (implies
     (natp n)
     (equal
      (logipedia-bigops-false-bigop
       n nil-value operation sequence)
      nil-value))))

(value-triple :itpeval-statement-checked)
:q
