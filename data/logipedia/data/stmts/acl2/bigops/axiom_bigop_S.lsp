;; Statement-only formalization of Logipedia corpus artifact
;; bigops.axiom_bigop_S: at every successor index, the source module's
;; abstract equality relates the polymorphic bigop and bigop_body function
;; values for every carrier. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-bigops-axiom-s-source-equal-p
  (h-type left-function right-function)
  t)

(defstub logipedia-bigops-axiom-s-bigop-function
  (h-type index)
  t)

(defstub logipedia-bigops-axiom-s-bigop-body-function
  (h-type index)
  t)

(defun-sk logipedia-bigops-axiom-bigop-s-statement ()
  (forall (h-type index)
    (implies
     (natp index)
     (logipedia-bigops-axiom-s-source-equal-p
      h-type
      (logipedia-bigops-axiom-s-bigop-function
       h-type (+ 1 index))
      (logipedia-bigops-axiom-s-bigop-body-function
       h-type (+ 1 index))))))

(value-triple :itpeval-statement-checked)
:q
