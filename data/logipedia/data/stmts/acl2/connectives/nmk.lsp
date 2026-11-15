;; Statement-only formalization of Logipedia corpus artifact
;; connectives.nmk, catalog title "connectives.nmk": negation introduction
;; for the module's abstract False and Not connectives: for every proposition
;; A, if A implies False, then Not A. This file contains no proof.

(in-package "ACL2")

;; ACL2 objects form the carrier of source propositions. These conservative
;; interfaces expose proposition truth and the source module's abstract False
;; and Not constants without imposing additional laws on them.
(defstub logipedia-connectives-nmk-holds-p
  (proposition)
  t)

(defstub logipedia-connectives-nmk-false-proposition
  ()
  t)

(defstub logipedia-connectives-nmk-not-proposition
  (proposition)
  t)

(defun-sk logipedia-connectives-nmk-statement ()
  (forall (a)
    (implies
     (implies
      (logipedia-connectives-nmk-holds-p a)
      (logipedia-connectives-nmk-holds-p
       (logipedia-connectives-nmk-false-proposition)))
     (logipedia-connectives-nmk-holds-p
      (logipedia-connectives-nmk-not-proposition a)))))

(value-triple :itpeval-statement-checked)
:q
