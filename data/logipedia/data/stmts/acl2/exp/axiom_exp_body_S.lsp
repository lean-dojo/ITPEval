;; Statement-only formalization of Logipedia corpus artifact
;; exp.axiom_exp_body_S, catalog title "exp.axiom_exp_body_S": for every
;; natural base and exponent, the exponentiation body at the successor
;; exponent equals the exponentiation value times the base. This file
;; contains no proof.

(in-package "ACL2")

;; NFIX wrappers retain the source constants' natural codomains without
;; proposition-level totality premises.

(defstub logipedia-exp-axiom-exp-body-s-exp-raw
  (base exponent)
  t)

(defstub logipedia-exp-axiom-exp-body-s-raw
  (base exponent)
  t)

(defun logipedia-exp-axiom-exp-body-s-exp (base exponent)
  (nfix
   (logipedia-exp-axiom-exp-body-s-exp-raw
    (nfix base)
    (nfix exponent))))

(defun logipedia-exp-axiom-exp-body-s (base exponent)
  (nfix
   (logipedia-exp-axiom-exp-body-s-raw
    (nfix base)
    (nfix exponent))))

(defun-sk logipedia-exp-axiom-exp-body-s-statement ()
  (forall (base exponent)
    (implies
     (and
      (natp base)
      (natp exponent))
     (equal
      (logipedia-exp-axiom-exp-body-s base (+ exponent 1))
      (* (logipedia-exp-axiom-exp-body-s-exp base exponent)
         base)))))

(value-triple :itpeval-statement-checked)
:q
