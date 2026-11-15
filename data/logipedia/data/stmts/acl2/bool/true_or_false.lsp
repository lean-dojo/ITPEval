;; Statement-only formalization of Logipedia corpus artifact
;; bool.true_or_false, catalog title "bool.true_or_false": every Boolean
;; value is equal to either true or false. This file contains no proof.

(in-package "ACL2")

(defun logipedia-bool-true-or-false-statement (b)
  (implies
   (booleanp b)
   (or (equal b t)
       (equal b nil))))

(value-triple :itpeval-statement-checked)
:q
