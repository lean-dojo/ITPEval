;; Statement-only formalization of Logipedia corpus artifact
;; bigops.bigop_Sfalse: when the Boolean selector at k is false, extending
;; the fold from k to k+1 leaves its value unchanged. This file contains no
;; proof.

(in-package "ACL2")

;; These conservative functions represent an arbitrary source predicate,
;; operation, sequence, and neutral value for each environment.

(defstub logipedia-bigops-sfalse-predicate
  (environment index)
  t)

(defstub logipedia-bigops-sfalse-operation
  (environment left right)
  t)

(defstub logipedia-bigops-sfalse-sequence
  (environment index)
  t)

(defstub logipedia-bigops-sfalse-neutral
  (environment)
  t)

(defun logipedia-bigops-sfalse-bigop (environment index)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (logipedia-bigops-sfalse-neutral environment)
    (let* ((prior-index (- index 1))
           (prior-value
            (logipedia-bigops-sfalse-bigop
             environment prior-index)))
      (if (logipedia-bigops-sfalse-predicate
           environment prior-index)
          (logipedia-bigops-sfalse-operation
           environment
           (logipedia-bigops-sfalse-sequence
            environment prior-index)
           prior-value)
        prior-value))))

(defun-sk logipedia-bigops-bigop-sfalse-statement ()
  (forall (environment k)
    (implies
     (and
      (natp k)
      (booleanp
       (logipedia-bigops-sfalse-predicate environment k))
      (equal
       (logipedia-bigops-sfalse-predicate environment k)
       nil))
     (equal
      (logipedia-bigops-sfalse-bigop environment (+ 1 k))
      (logipedia-bigops-sfalse-bigop environment k)))))

(value-triple :itpeval-statement-checked)
:q
