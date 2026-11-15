;; Statement-only formalization of Logipedia corpus artifact
;; bigops.axiom_bigop_O: at index zero, the source module's abstract equality
;; relates the polymorphic bigop and bigop_body function values for every
;; carrier. This file contains no proof.

(in-package "ACL2")

;; Function values and the source's opaque connectives.equal relation are
;; reified conservatively. In particular, this does not replace that relation
;; with ACL2 equality or weaken function-value equality to pointwise agreement.

(defstub logipedia-bigops-axiom-o-source-equal-p
  (h-type left-function right-function)
  t)

(defstub logipedia-bigops-axiom-o-bigop-function
  (h-type index)
  t)

(defstub logipedia-bigops-axiom-o-bigop-body-function
  (h-type index)
  t)

(defun-sk logipedia-bigops-axiom-bigop-o-statement ()
  (forall (h-type)
    (logipedia-bigops-axiom-o-source-equal-p
     h-type
     (logipedia-bigops-axiom-o-bigop-function h-type 0)
     (logipedia-bigops-axiom-o-bigop-body-function h-type 0))))

(value-triple :itpeval-statement-checked)
:q
