;; Statement-only formalization of Logipedia corpus artifact
;; connectives.match_And_prop, catalog title "connectives.match_And_prop":
;; elimination for the module's abstract And connective, stating that a
;; continuation from A and B to an arbitrary return proposition, together
;; with And A B, entails that return proposition. This file contains no proof.

(in-package "ACL2")

;; ACL2 objects form the carrier of source propositions. These conservative
;; interfaces expose proposition truth and the source module's abstract And
;; connective without imposing any additional laws on it.
(defstub logipedia-connectives-match-and-prop-holds-p
  (proposition)
  t)

(defstub logipedia-connectives-match-and-prop-and-proposition
  (left-proposition right-proposition)
  t)

(defun logipedia-connectives-match-and-prop-statement
  (a b return-proposition)
  (implies
   (implies
    (logipedia-connectives-match-and-prop-holds-p a)
    (implies
     (logipedia-connectives-match-and-prop-holds-p b)
     (logipedia-connectives-match-and-prop-holds-p return-proposition)))
   (implies
    (logipedia-connectives-match-and-prop-holds-p
     (logipedia-connectives-match-and-prop-and-proposition a b))
    (logipedia-connectives-match-and-prop-holds-p return-proposition))))

(value-triple :itpeval-statement-checked)
:q
