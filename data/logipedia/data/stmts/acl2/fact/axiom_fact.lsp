;; Statement-only formalization of Logipedia corpus artifact fact.axiom_fact,
;; catalog title "fact.axiom_fact": for every natural number, the source's
;; abstract equality relates factorial to its natural-filtered body.
;; This file contains no proof.

(in-package "ACL2")

;; NFIX wrappers encode the source constants' Nat -> Nat types without
;; weakening the unconditional source axiom with range-typing hypotheses.

(defstub logipedia-fact-axiom-fact-raw
  (n)
  t)

(defstub logipedia-fact-axiom-fact-filtered-body-raw
  (n)
  t)

(defun logipedia-fact-axiom-fact (n)
  (nfix
   (logipedia-fact-axiom-fact-raw
    (nfix n))))

(defun logipedia-fact-axiom-fact-filtered-body (n)
  (nfix
   (logipedia-fact-axiom-fact-filtered-body-raw
    (nfix n))))

;; The second interface represents the fixed composite
;; filter_nat_type(fact_body); it is not defined to be fact_body.

(defun-sk logipedia-fact-axiom-fact-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-fact-axiom-fact n)
      (logipedia-fact-axiom-fact-filtered-body n)))))

(value-triple :itpeval-statement-checked)
:q
