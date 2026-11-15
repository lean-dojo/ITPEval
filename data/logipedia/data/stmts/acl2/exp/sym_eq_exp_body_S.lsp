;; Statement-only formalization of Logipedia corpus artifact
;; exp.sym_eq_exp_body_S, catalog title "exp.sym_eq_exp_body_S": for every
;; natural base and exponent, the exponentiation value times the base is
;; Leibniz-equal to the exponentiation body at the successor exponent. This
;; file contains no proof.

(in-package "ACL2")

;; NFIX wrappers retain both source constants' natural codomains without
;; adding totality hypotheses to the theorem.

(defstub logipedia-exp-sym-eq-exp-body-s-exp-raw
  (base exponent)
  t)

(defstub logipedia-exp-sym-eq-exp-body-s-raw
  (base exponent)
  t)

(defun logipedia-exp-sym-eq-exp-body-s-exp (base exponent)
  (nfix
   (logipedia-exp-sym-eq-exp-body-s-exp-raw
    (nfix base)
    (nfix exponent))))

(defun logipedia-exp-sym-eq-exp-body-s (base exponent)
  (nfix
   (logipedia-exp-sym-eq-exp-body-s-raw
    (nfix base)
    (nfix exponent))))

(defun-sk logipedia-exp-sym-eq-exp-body-s-statement ()
  (forall (base exponent)
    (implies
     (and
      (natp base)
      (natp exponent))
     (equal
      (* (logipedia-exp-sym-eq-exp-body-s-exp base exponent)
         base)
      (logipedia-exp-sym-eq-exp-body-s base (+ exponent 1))))))

(value-triple :itpeval-statement-checked)
:q
