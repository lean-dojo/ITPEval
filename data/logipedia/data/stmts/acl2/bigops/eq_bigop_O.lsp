;; Statement-only formalization of Logipedia corpus artifact
;; bigops.eq_bigop_O: at index zero, bigop and bigop_body are Leibniz-equal
;; at their polymorphic function type. This file contains no proof.

(in-package "ACL2")

;; ACL2 equality of reified function values represents the source's Leibniz
;; equality at the complete higher-order function type.

(defstub logipedia-bigops-eq-o-bigop-function
  (h-type index)
  t)

(defstub logipedia-bigops-eq-o-bigop-body-function
  (h-type index)
  t)

(defun-sk logipedia-bigops-eq-bigop-o-statement ()
  (forall (h-type)
    (equal
     (logipedia-bigops-eq-o-bigop-function h-type 0)
     (logipedia-bigops-eq-o-bigop-body-function h-type 0))))

(value-triple :itpeval-statement-checked)
:q
