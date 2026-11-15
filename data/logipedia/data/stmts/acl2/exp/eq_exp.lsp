;; Statement-only formalization of Logipedia corpus artifact exp.eq_exp,
;; catalog title "exp.eq_exp": for every pair of natural numbers, the
;; exponentiation value is Leibniz-equal to its natural-filtered body.
;; This file contains no proof.

(in-package "ACL2")

;; NFIX wrappers represent the source constants as total natural-valued
;; functions without making their totality an antecedent of the theorem.

(defstub logipedia-exp-eq-exp-raw
  (base exponent)
  t)

(defstub logipedia-exp-eq-exp-body-raw
  (base exponent)
  t)

(defun logipedia-exp-eq-exp (base exponent)
  (nfix
   (logipedia-exp-eq-exp-raw
    (nfix base)
    (nfix exponent))))

(defun logipedia-exp-eq-exp-body (base exponent)
  (nfix
   (logipedia-exp-eq-exp-body-raw
    (nfix base)
    (nfix exponent))))

;; On natural indices, filter_nat_type is extensionally the identity.
(defun logipedia-exp-eq-exp-filtered-body (base exponent)
  (logipedia-exp-eq-exp-body base exponent))

;; Leibniz equality is equivalent to identity in this direction.
(defun-sk logipedia-exp-eq-exp-statement ()
  (forall (base exponent)
    (implies
     (and
      (natp base)
      (natp exponent))
     (equal
      (logipedia-exp-eq-exp base exponent)
      (logipedia-exp-eq-exp-filtered-body base exponent)))))

(value-triple :itpeval-statement-checked)
:q
