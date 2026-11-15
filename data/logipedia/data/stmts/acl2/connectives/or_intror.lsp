;; Statement-only formalization of Logipedia corpus artifact
;; connectives.or_intror, catalog title "connectives.or_intror": right
;; introduction for the module's abstract Or connective, stating that Or A B
;; holds whenever proposition B holds. This file contains no proof.

(in-package "ACL2")

;; ACL2 objects form the carrier of source propositions. These conservative
;; interfaces expose proposition truth and the source module's abstract Or
;; connective without imposing any additional laws on it.
(defstub logipedia-connectives-or-intror-holds-p
  (proposition)
  t)

(defstub logipedia-connectives-or-intror-or-proposition
  (left-proposition right-proposition)
  t)

(defun logipedia-connectives-or-intror-statement (a b)
  (implies
   (logipedia-connectives-or-intror-holds-p b)
   (logipedia-connectives-or-intror-holds-p
    (logipedia-connectives-or-intror-or-proposition a b))))

(value-triple :itpeval-statement-checked)
:q
