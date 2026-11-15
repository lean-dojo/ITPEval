;; Statement-only formalization of Logipedia corpus artifact
;; connectives.Not_ind, catalog title "connectives.Not_ind": for arbitrary
;; propositions A and Q, a continuation from A implying the module's False
;; proposition to Q, together with the module's abstract Not A, entails Q.
;; This file contains no proof.

(in-package "ACL2")

;; ACL2 objects form the carrier of source propositions.  These conservative
;; interfaces expose proposition truth and the source module's abstract False
;; and Not constants without imposing additional laws on them.
(defstub logipedia-connectives-not-ind-holds-p
  (proposition)
  t)

(defstub logipedia-connectives-not-ind-false-proposition
  ()
  t)

(defstub logipedia-connectives-not-ind-not-proposition
  (proposition)
  t)

(defun logipedia-connectives-not-ind-statement (a q)
  (implies
   (implies
    (implies
     (logipedia-connectives-not-ind-holds-p a)
     (logipedia-connectives-not-ind-holds-p
      (logipedia-connectives-not-ind-false-proposition)))
    (logipedia-connectives-not-ind-holds-p q))
   (implies
    (logipedia-connectives-not-ind-holds-p
     (logipedia-connectives-not-ind-not-proposition a))
    (logipedia-connectives-not-ind-holds-p q))))

(value-triple :itpeval-statement-checked)
:q
