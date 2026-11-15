;; Statement-only formalization of Logipedia corpus artifact exp.sym_eq_exp,
;; catalog title "exp.sym_eq_exp": for every pair of natural numbers, the
;; natural-filtered exponentiation body is Leibniz-equal to the exponentiation
;; value. This file contains no proof.

(in-package "ACL2")

;; Raw conservative interfaces are wrapped with NFIX so that the represented
;; source constants retain their nat -> nat -> nat types without adding any
;; hypothesis to the proposition. Every natural-valued binary function is
;; represented by a suitable interpretation of its raw stub.

(defstub logipedia-exp-sym-eq-exp-raw
  (base exponent)
  t)

(defstub logipedia-exp-sym-eq-exp-body-raw
  (base exponent)
  t)

(defun logipedia-exp-sym-eq-exp (base exponent)
  (nfix
   (logipedia-exp-sym-eq-exp-raw
    (nfix base)
    (nfix exponent))))

(defun logipedia-exp-sym-eq-exp-body (base exponent)
  (nfix
   (logipedia-exp-sym-eq-exp-body-raw
    (nfix base)
    (nfix exponent))))

;; The source filter_nat_type agrees with its function argument at every
;; natural. Specializing it to exp_body is therefore represented directly by
;; applying the typed body function.
(defun logipedia-exp-sym-eq-exp-filtered-body (base exponent)
  (logipedia-exp-sym-eq-exp-body base exponent))

;; Leibniz equality is bidirectionally equivalent to identity: identity
;; transports every predicate, and the converse uses the predicate z = x.
(defun-sk logipedia-exp-sym-eq-exp-statement ()
  (forall (base exponent)
    (implies
     (and
      (natp base)
      (natp exponent))
     (equal
      (logipedia-exp-sym-eq-exp-filtered-body base exponent)
      (logipedia-exp-sym-eq-exp base exponent)))))

(value-triple :itpeval-statement-checked)
:q
