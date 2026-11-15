;; Statement-only formalization of Logipedia corpus artifact
;; fact.eq_fact_body_O, catalog title "fact.eq_fact_body_O":
;; the factorial body at zero is Leibniz-equal to one.
;; This file contains no proof.

(in-package "ACL2")

(defstub logipedia-fact-eq-fact-body-o-raw
  (n)
  t)

(defun logipedia-fact-eq-fact-body-o (n)
  (nfix
   (logipedia-fact-eq-fact-body-o-raw
    (nfix n))))

(defun logipedia-fact-eq-fact-body-o-statement ()
  (equal
   (logipedia-fact-eq-fact-body-o 0)
   1))

(value-triple :itpeval-statement-checked)
:q
