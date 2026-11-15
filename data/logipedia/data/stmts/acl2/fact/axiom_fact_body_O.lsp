;; Statement-only formalization of Logipedia corpus artifact
;; fact.axiom_fact_body_O, catalog title "fact.axiom_fact_body_O":
;; the source equality relates the factorial body at zero to one.
;; This file contains no proof.

(in-package "ACL2")

(defstub logipedia-fact-axiom-fact-body-o-raw
  (n)
  t)

(defun logipedia-fact-axiom-fact-body-o (n)
  (nfix
   (logipedia-fact-axiom-fact-body-o-raw
    (nfix n))))

(defun logipedia-fact-axiom-fact-body-o-statement ()
  (equal
   (logipedia-fact-axiom-fact-body-o 0)
   1))

(value-triple :itpeval-statement-checked)
:q
