;; Statement-only formalization of Logipedia corpus artifact
;; bigops.eq_bigop_S: at every successor index, bigop and bigop_body are
;; Leibniz-equal at their polymorphic function type.
;; This file contains no proof.

(in-package "ACL2")

(defstub logipedia-bigops-eq-s-bigop-function
  (h-type index)
  t)

(defstub logipedia-bigops-eq-s-bigop-body-function
  (h-type index)
  t)

(defun-sk logipedia-bigops-eq-bigop-s-statement ()
  (forall (h-type index)
    (implies
     (natp index)
     (equal
      (logipedia-bigops-eq-s-bigop-function
       h-type (+ 1 index))
      (logipedia-bigops-eq-s-bigop-body-function
       h-type (+ 1 index))))))

(value-triple :itpeval-statement-checked)
:q
