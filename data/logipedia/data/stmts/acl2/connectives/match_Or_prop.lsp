;; Statement-only formalization of Logipedia corpus artifact
;; connectives.match_Or_prop, catalog title "connectives.match_Or_prop":
;; elimination for the module's abstract Or connective, stating that
;; continuations from A and B to an arbitrary return proposition, together
;; with Or A B, entail that return proposition. This file contains no proof.

(in-package "ACL2")

;; ACL2 objects form the carrier of source propositions. These conservative
;; interfaces expose proposition truth and the source module's abstract Or
;; connective without imposing any additional laws on it.
(defstub logipedia-connectives-match-or-prop-holds-p
  (proposition)
  t)

(defstub logipedia-connectives-match-or-prop-or-proposition
  (left-proposition right-proposition)
  t)

(defun logipedia-connectives-match-or-prop-statement
  (a b return-proposition)
  (implies
   (implies
    (logipedia-connectives-match-or-prop-holds-p a)
    (logipedia-connectives-match-or-prop-holds-p return-proposition))
   (implies
    (implies
     (logipedia-connectives-match-or-prop-holds-p b)
     (logipedia-connectives-match-or-prop-holds-p return-proposition))
    (implies
     (logipedia-connectives-match-or-prop-holds-p
      (logipedia-connectives-match-or-prop-or-proposition a b))
     (logipedia-connectives-match-or-prop-holds-p return-proposition)))))

(value-triple :itpeval-statement-checked)
:q
