;; Statement-only formalization of Logipedia corpus artifact
;; bool.sym_eq_match_bool_type_true: the true-branch value is equal to the
;; polymorphic Boolean eliminator applied to true. This file contains no
;; proof.

(in-package "ACL2")

;; A source return type is represented by ACL2's full value universe.  The
;; eliminator itself is definitional, so no type tags, membership predicates,
;; or potentially empty coded function spaces are needed.

(defun logipedia-bool-match (case-true case-false boolean-value)
  (if boolean-value case-true case-false))

(defun-sk logipedia-bool-sym-eq-match-type-true-statement ()
  (forall (case-true case-false)
    (equal
     case-true
     (logipedia-bool-match case-true case-false t))))

(value-triple :itpeval-statement-checked)
:q
