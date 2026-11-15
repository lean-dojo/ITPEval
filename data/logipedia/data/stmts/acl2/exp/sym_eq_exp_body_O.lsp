;; Statement-only formalization of Logipedia corpus artifact
;; exp.sym_eq_exp_body_O, catalog title "exp.sym_eq_exp_body_O":
;; for every natural number base, the natural number one is Leibniz-equal
;; to the exponentiation body at exponent zero. This file contains no proof.

(in-package "ACL2")

;; NFIX represents the source constant's natural codomain definitionally.

(defstub logipedia-exp-sym-eq-exp-body-o-raw
  (base exponent)
  t)

(defun logipedia-exp-sym-eq-exp-body-o (base exponent)
  (nfix
   (logipedia-exp-sym-eq-exp-body-o-raw
    (nfix base)
    (nfix exponent))))

(defun-sk logipedia-exp-sym-eq-exp-body-o-statement ()
  (forall (base)
    (implies
     (natp base)
     (equal
      1
      (logipedia-exp-sym-eq-exp-body-o base 0)))))

(value-triple :itpeval-statement-checked)
:q
