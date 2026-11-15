;; Statement-only formalization of Logipedia corpus artifact
;; bigops.sym_eq_bigop_S: at every successor index, bigop_body is
;; Leibniz-equal to bigop at their polymorphic function type.
;; This file contains no proof.

(in-package "ACL2")

(defstub logipedia-bigops-sym-s-bigop-function
  (h-type index)
  t)

(defstub logipedia-bigops-sym-s-bigop-body-function
  (h-type index)
  t)

(defun-sk logipedia-bigops-sym-eq-bigop-s-statement ()
  (forall (h-type index)
    (implies
     (natp index)
     (equal
      (logipedia-bigops-sym-s-bigop-body-function
       h-type (+ 1 index))
      (logipedia-bigops-sym-s-bigop-function
       h-type (+ 1 index))))))

(value-triple :itpeval-statement-checked)
:q
