;; Statement-only formalization of Logipedia corpus artifact exp.axiom_exp,
;; catalog title "exp.axiom_exp": for every pair of natural numbers, the
;; exponentiation function equals its natural-filtered body at that pair.
;; This file contains no proof.

(in-package "ACL2")

;; ACL2 stubs are untyped. NFIX wrappers represent the source constants as
;; total Nat -> Nat -> Nat functions without adding totality hypotheses.

(defstub logipedia-exp-axiom-exp-raw
  (base exponent)
  t)

(defstub logipedia-exp-axiom-exp-body-raw
  (base exponent)
  t)

(defun logipedia-exp-axiom-exp (base exponent)
  (nfix
   (logipedia-exp-axiom-exp-raw
    (nfix base)
    (nfix exponent))))

(defun logipedia-exp-axiom-exp-body (base exponent)
  (nfix
   (logipedia-exp-axiom-exp-body-raw
    (nfix base)
    (nfix exponent))))

;; This is the source module's opaque connectives.equal specialized to Nat.
;; It must not be identified with ACL2's native EQUAL in an axiom artifact.
(defstub logipedia-exp-axiom-exp-source-equal-p
  (left right)
  t)

;; On natural indices, filter_nat_type is extensionally the identity.
(defun logipedia-exp-axiom-exp-filtered-body (base exponent)
  (logipedia-exp-axiom-exp-body base exponent))

(defun-sk logipedia-exp-axiom-exp-statement ()
  (forall (base exponent)
    (implies
     (and
      (natp base)
      (natp exponent))
     (logipedia-exp-axiom-exp-source-equal-p
      (logipedia-exp-axiom-exp base exponent)
      (logipedia-exp-axiom-exp-filtered-body base exponent)))))

(value-triple :itpeval-statement-checked)
:q
