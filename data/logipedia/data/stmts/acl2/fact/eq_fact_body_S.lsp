;; Statement-only formalization of Logipedia corpus artifact
;; fact.eq_fact_body_S, catalog title "fact.eq_fact_body_S": for every natural
;; number, the factorial body at its successor is Leibniz-equal to the
;; factorial value times that successor. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-fact-eq-fact-body-s-fact-raw
  (n)
  t)

(defstub logipedia-fact-eq-fact-body-s-raw
  (n)
  t)

(defun logipedia-fact-eq-fact-body-s-fact (n)
  (nfix
   (logipedia-fact-eq-fact-body-s-fact-raw
    (nfix n))))

(defun logipedia-fact-eq-fact-body-s (n)
  (nfix
   (logipedia-fact-eq-fact-body-s-raw
    (nfix n))))

(defun-sk logipedia-fact-eq-fact-body-s-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-fact-eq-fact-body-s (+ n 1))
      (* (logipedia-fact-eq-fact-body-s-fact n)
         (+ n 1))))))

(value-triple :itpeval-statement-checked)
:q
