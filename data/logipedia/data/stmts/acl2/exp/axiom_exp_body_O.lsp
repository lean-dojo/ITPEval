;; Statement-only formalization of Logipedia corpus artifact
;; exp.axiom_exp_body_O, catalog title "exp.axiom_exp_body_O":
;; for every natural number base, the exponentiation body at exponent zero
;; is the natural number one. This file contains no proof.

(in-package "ACL2")

;; NFIX gives the source constant its Nat -> Nat -> Nat result type without a
;; proposition-level totality premise.

(defstub logipedia-exp-axiom-exp-body-o-raw
  (base exponent)
  t)

(defun logipedia-exp-axiom-exp-body-o (base exponent)
  (nfix
   (logipedia-exp-axiom-exp-body-o-raw
    (nfix base)
    (nfix exponent))))

(defun-sk logipedia-exp-axiom-exp-body-o-statement ()
  (forall (base)
    (implies
     (natp base)
     (equal
      (logipedia-exp-axiom-exp-body-o base 0)
      1))))

(value-triple :itpeval-statement-checked)
:q
