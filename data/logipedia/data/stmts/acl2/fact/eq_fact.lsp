;; Statement-only formalization of Logipedia corpus artifact fact.eq_fact,
;; catalog title "fact.eq_fact": for every natural number, factorial is
;; Leibniz-equal to its natural-filtered body. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-fact-eq-fact-raw
  (n)
  t)

(defstub logipedia-fact-eq-fact-body-raw
  (n)
  t)

(defun logipedia-fact-eq-fact (n)
  (nfix
   (logipedia-fact-eq-fact-raw
    (nfix n))))

(defun logipedia-fact-eq-fact-body (n)
  (nfix
   (logipedia-fact-eq-fact-body-raw
    (nfix n))))

(defun logipedia-fact-eq-fact-filtered-body (n)
  (logipedia-fact-eq-fact-body n))

;; Leibniz equality is extensionally equivalent to identity here.
(defun-sk logipedia-fact-eq-fact-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-fact-eq-fact n)
      (logipedia-fact-eq-fact-filtered-body n)))))

(value-triple :itpeval-statement-checked)
:q
