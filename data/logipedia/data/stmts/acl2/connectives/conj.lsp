;; Statement-only formalization of Logipedia corpus artifact
;; connectives.conj, catalog title "connectives.conj": conjunction
;; introduction for the module's abstract And connective, stating that
;; And A B holds whenever propositions A and B hold. This file contains no
;; proof.

(in-package "ACL2")

;; ACL2 objects form the carrier of source propositions. These conservative
;; interfaces expose proposition truth and the source module's abstract And
;; connective without imposing any additional laws on it.
(defstub logipedia-connectives-conj-holds-p
  (proposition)
  t)

(defstub logipedia-connectives-conj-and-proposition
  (left-proposition right-proposition)
  t)

(defun logipedia-connectives-conj-statement (a b)
  (implies
   (logipedia-connectives-conj-holds-p a)
   (implies
    (logipedia-connectives-conj-holds-p b)
    (logipedia-connectives-conj-holds-p
     (logipedia-connectives-conj-and-proposition a b)))))

(value-triple :itpeval-statement-checked)
:q
