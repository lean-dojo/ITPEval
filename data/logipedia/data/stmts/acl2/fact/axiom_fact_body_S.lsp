;; Statement-only formalization of Logipedia corpus artifact
;; fact.axiom_fact_body_S, catalog title "fact.axiom_fact_body_S": for every
;; natural number, the source equality relates the factorial body at its
;; successor to the factorial value times that successor. This file contains
;; no proof.

(in-package "ACL2")

(defstub logipedia-fact-axiom-fact-body-s-fact-raw
  (n)
  t)

(defstub logipedia-fact-axiom-fact-body-s-raw
  (n)
  t)

(defun logipedia-fact-axiom-fact-body-s-fact (n)
  (nfix
   (logipedia-fact-axiom-fact-body-s-fact-raw
    (nfix n))))

(defun logipedia-fact-axiom-fact-body-s (n)
  (nfix
   (logipedia-fact-axiom-fact-body-s-raw
    (nfix n))))

(defstub logipedia-fact-axiom-fact-body-s-source-equal-p
  (left right)
  t)

(defun-sk logipedia-fact-axiom-fact-body-s-statement ()
  (forall (n)
    (implies
     (natp n)
     (logipedia-fact-axiom-fact-body-s-source-equal-p
      (logipedia-fact-axiom-fact-body-s (+ n 1))
      (* (logipedia-fact-axiom-fact-body-s-fact n)
         (+ n 1))))))

(value-triple :itpeval-statement-checked)
:q
