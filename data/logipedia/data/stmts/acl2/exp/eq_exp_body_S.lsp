;; Statement-only formalization of Logipedia corpus artifact
;; exp.eq_exp_body_S, catalog title "exp.eq_exp_body_S": for every natural
;; base and exponent, the exponentiation body at the successor exponent is
;; Leibniz-equal to the exponentiation value times the base. This file
;; contains no proof.

(in-package "ACL2")

;; NFIX wrappers retain both source constants' natural codomains without
;; adding totality hypotheses to the theorem.

(defstub logipedia-exp-eq-exp-body-s-exp-raw
  (base exponent)
  t)

(defstub logipedia-exp-eq-exp-body-s-raw
  (base exponent)
  t)

(defun logipedia-exp-eq-exp-body-s-exp (base exponent)
  (nfix
   (logipedia-exp-eq-exp-body-s-exp-raw
    (nfix base)
    (nfix exponent))))

(defun logipedia-exp-eq-exp-body-s (base exponent)
  (nfix
   (logipedia-exp-eq-exp-body-s-raw
    (nfix base)
    (nfix exponent))))

(defun-sk logipedia-exp-eq-exp-body-s-statement ()
  (forall (base exponent)
    (implies
     (and
      (natp base)
      (natp exponent))
     (equal
      (logipedia-exp-eq-exp-body-s base (+ exponent 1))
      (* (logipedia-exp-eq-exp-body-s-exp base exponent)
         base)))))

(value-triple :itpeval-statement-checked)
:q
