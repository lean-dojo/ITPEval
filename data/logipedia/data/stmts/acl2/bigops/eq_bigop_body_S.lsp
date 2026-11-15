;; Statement-only formalization of Logipedia corpus artifact
;; bigops.eq_bigop_body_S: the successor body is Leibniz-equal to the
;; Boolean-controlled step using bigop. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-bigops-eq-body-s-predicate
  (environment index)
  t)

(defstub logipedia-bigops-eq-body-s-operation
  (environment left right)
  t)

(defstub logipedia-bigops-eq-body-s-sequence
  (environment index)
  t)

(defstub logipedia-bigops-eq-body-s-bigop
  (environment index)
  t)

(defstub logipedia-bigops-eq-body-s-bigop-body
  (environment index)
  t)

(defun-sk logipedia-bigops-eq-bigop-body-s-statement ()
  (forall (environment index)
    (implies
     (and
      (natp index)
      (booleanp
       (logipedia-bigops-eq-body-s-predicate
        environment index)))
     (equal
      (logipedia-bigops-eq-body-s-bigop-body
       environment (+ 1 index))
      (if (logipedia-bigops-eq-body-s-predicate
           environment index)
          (logipedia-bigops-eq-body-s-operation
           environment
           (logipedia-bigops-eq-body-s-sequence
            environment index)
           (logipedia-bigops-eq-body-s-bigop
            environment index))
        (logipedia-bigops-eq-body-s-bigop
         environment index))))))

(value-triple :itpeval-statement-checked)
:q
