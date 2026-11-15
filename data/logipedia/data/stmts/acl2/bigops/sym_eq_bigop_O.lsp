;; Statement-only formalization of Logipedia corpus artifact
;; bigops.sym_eq_bigop_O: at index zero, bigop_body is Leibniz-equal to
;; bigop at their polymorphic function type. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-bigops-sym-o-bigop-function
  (h-type index)
  t)

(defstub logipedia-bigops-sym-o-bigop-body-function
  (h-type index)
  t)

(defun-sk logipedia-bigops-sym-eq-bigop-o-statement ()
  (forall (h-type)
    (equal
     (logipedia-bigops-sym-o-bigop-body-function h-type 0)
     (logipedia-bigops-sym-o-bigop-function h-type 0))))

(value-triple :itpeval-statement-checked)
:q
