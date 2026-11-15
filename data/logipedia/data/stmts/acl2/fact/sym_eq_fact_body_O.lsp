;; Statement-only formalization of Logipedia corpus artifact
;; fact.sym_eq_fact_body_O, catalog title "fact.sym_eq_fact_body_O":
;; one is Leibniz-equal to the factorial body at zero.
;; This file contains no proof.

(in-package "ACL2")

(defstub logipedia-fact-sym-eq-fact-body-o-raw
  (n)
  t)

(defun logipedia-fact-sym-eq-fact-body-o (n)
  (nfix
   (logipedia-fact-sym-eq-fact-body-o-raw
    (nfix n))))

(defun logipedia-fact-sym-eq-fact-body-o-statement ()
  (equal
   1
   (logipedia-fact-sym-eq-fact-body-o 0)))

(value-triple :itpeval-statement-checked)
:q
