;; Statement-only formalization of Logipedia corpus artifact
;; exp.eq_exp_body_O, catalog title "exp.eq_exp_body_O":
;; for every natural number base, the exponentiation body at exponent zero
;; is Leibniz-equal to the natural number one. This file contains no proof.

(in-package "ACL2")

;; NFIX represents the source constant's natural codomain definitionally.

(defstub logipedia-exp-eq-exp-body-o-raw
  (base exponent)
  t)

(defun logipedia-exp-eq-exp-body-o (base exponent)
  (nfix
   (logipedia-exp-eq-exp-body-o-raw
    (nfix base)
    (nfix exponent))))

(defun-sk logipedia-exp-eq-exp-body-o-statement ()
  (forall (base)
    (implies
     (natp base)
     (equal
      (logipedia-exp-eq-exp-body-o base 0)
      1))))

(value-triple :itpeval-statement-checked)
:q
