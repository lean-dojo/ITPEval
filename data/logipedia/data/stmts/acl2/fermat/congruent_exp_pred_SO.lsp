;; Statement-only formalization of Logipedia corpus artifact
;; fermat.congruent_exp_pred_SO, catalog title
;; "fermat.congruent_exp_pred_SO": Fermat's little theorem in congruence form,
;; stating that a natural number not divisible by a natural prime has
;; exponent p - 1 congruent to one modulo p. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-fermat-congruent-exp-pred-so-divides-p
    (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

(defun-sk logipedia-fermat-congruent-exp-pred-so-prime-divisors-p
    (p)
  (forall (m)
    (implies
     (and
      (natp m)
      (logipedia-fermat-congruent-exp-pred-so-divides-p m p)
      (< 1 m))
     (equal m p))))

(defun logipedia-fermat-congruent-exp-pred-so-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (logipedia-fermat-congruent-exp-pred-so-prime-divisors-p p)))

(defun logipedia-fermat-congruent-exp-pred-so-statement (p a)
  (implies
   (and
    (natp p)
    (natp a)
    (logipedia-fermat-congruent-exp-pred-so-prime-p p)
    (not
     (logipedia-fermat-congruent-exp-pred-so-divides-p p a)))
   (equal
    (mod (expt a (- p 1)) p)
    (mod 1 p))))

(value-triple :itpeval-statement-checked)
:q
