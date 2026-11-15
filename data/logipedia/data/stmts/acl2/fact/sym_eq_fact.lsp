;; Statement-only formalization of Logipedia corpus artifact fact.sym_eq_fact,
;; catalog title "fact.sym_eq_fact": for every natural number, the
;; natural-filtered factorial body is Leibniz-equal to factorial.
;; This file contains no proof.

(in-package "ACL2")

(defstub logipedia-fact-sym-eq-fact-raw
  (n)
  t)

(defstub logipedia-fact-sym-eq-fact-body-raw
  (n)
  t)

(defun logipedia-fact-sym-eq-fact (n)
  (nfix
   (logipedia-fact-sym-eq-fact-raw
    (nfix n))))

(defun logipedia-fact-sym-eq-fact-body (n)
  (nfix
   (logipedia-fact-sym-eq-fact-body-raw
    (nfix n))))

(defun logipedia-fact-sym-eq-fact-filtered-body (n)
  (logipedia-fact-sym-eq-fact-body n))

(defun-sk logipedia-fact-sym-eq-fact-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-fact-sym-eq-fact-filtered-body n)
      (logipedia-fact-sym-eq-fact n)))))

(value-triple :itpeval-statement-checked)
:q
