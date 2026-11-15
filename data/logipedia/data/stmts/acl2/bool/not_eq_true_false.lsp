;; Statement-only formalization of Logipedia corpus artifact
;; bool.not_eq_true_false, catalog title "bool.not_eq_true_false":
;; the Boolean value true is not equal to the Boolean value false.
;; This file contains no proof.

(in-package "ACL2")

(defun logipedia-bool-not-eq-true-false-statement ()
  (not (equal t nil)))

(value-triple :itpeval-statement-checked)
:q
