;; Statement-only formalization of Logipedia corpus artifact logic.proj1,
;; catalog title "logic.proj1": first projection from the module's abstract
;; conjunction, stating that A follows from And A B. This file contains no
;; proof.

(in-package "ACL2")

;; ACL2 objects form the carrier of source propositions. These conservative
;; interfaces expose proposition truth and the source module's abstract And
;; connective without imposing any additional laws on it.
(defstub logipedia-logic-proj1-holds-p
  (proposition)
  t)

(defstub logipedia-logic-proj1-and-proposition
  (left-proposition right-proposition)
  t)

(defun logipedia-logic-proj1-statement (a b)
  (implies
   (logipedia-logic-proj1-holds-p
    (logipedia-logic-proj1-and-proposition a b))
   (logipedia-logic-proj1-holds-p a)))

(value-triple :itpeval-statement-checked)
:q
