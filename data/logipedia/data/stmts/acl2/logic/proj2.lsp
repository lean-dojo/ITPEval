;; Statement-only formalization of Logipedia corpus artifact logic.proj2,
;; catalog title "logic.proj2": second projection from the module's abstract
;; conjunction, stating that B follows from And A B. This file contains no
;; proof.

(in-package "ACL2")

;; ACL2 objects form the carrier of source propositions. These conservative
;; interfaces expose proposition truth and the source module's abstract And
;; connective without imposing any additional laws on it.
(defstub logipedia-logic-proj2-holds-p
  (proposition)
  t)

(defstub logipedia-logic-proj2-and-proposition
  (left-proposition right-proposition)
  t)

(defun logipedia-logic-proj2-statement (a b)
  (implies
   (logipedia-logic-proj2-holds-p
    (logipedia-logic-proj2-and-proposition a b))
   (logipedia-logic-proj2-holds-p b)))

(value-triple :itpeval-statement-checked)
:q
