;; Statement-only formalization of Logipedia corpus artifact
;; bool.match_bool_prop, catalog title "bool.match_bool_prop": every
;; proposition-valued predicate on Boolean values that holds at true and
;; false holds for every Boolean value. This file contains no proof.

(in-package "ACL2")

;; This conservative interface represents the source's arbitrary predicate
;; bool -> Prop. Its use in Boolean positions gives ACL2's proposition-valued
;; interpretation without imposing any additional law.

(defstub logipedia-bool-match-prop-return-p
  (boolean-value)
  t)

(defun-sk logipedia-bool-match-prop-all-p ()
  (forall (boolean-value)
    (implies
     (booleanp boolean-value)
     (logipedia-bool-match-prop-return-p boolean-value))))

(defun logipedia-bool-match-prop-statement ()
  (implies
   (logipedia-bool-match-prop-return-p t)
   (implies
    (logipedia-bool-match-prop-return-p nil)
    (logipedia-bool-match-prop-all-p))))

(value-triple :itpeval-statement-checked)
:q
