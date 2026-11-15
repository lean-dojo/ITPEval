;; Statement-only formalization of Logipedia corpus artifact
;; connectives.or_introl, catalog title "connectives.or_introl": left
;; introduction for the module's abstract Or connective, stating that Or A B
;; holds whenever proposition A holds. This file contains no proof.

(in-package "ACL2")

;; ACL2 objects form the carrier of source propositions. These conservative
;; interfaces expose proposition truth and the source module's abstract Or
;; connective without imposing any additional laws on it.
(defstub logipedia-connectives-or-introl-holds-p
  (proposition)
  t)

(defstub logipedia-connectives-or-introl-or-proposition
  (left-proposition right-proposition)
  t)

(defun logipedia-connectives-or-introl-statement (a b)
  (implies
   (logipedia-connectives-or-introl-holds-p a)
   (logipedia-connectives-or-introl-holds-p
    (logipedia-connectives-or-introl-or-proposition a b))))

(value-triple :itpeval-statement-checked)
:q
