;; Statement-only formalization of Logipedia corpus artifact
;; bool.axiom_match_bool_type_true, catalog title
;; "bool.axiom_match_bool_type_true": for every return type and two values
;; of that type, the polymorphic Boolean eliminator applied to true equals
;; its true-branch value. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for arbitrary return types and the source's
;; polymorphic Boolean eliminator.

(defstub logipedia-bool-match-true-member-p
  (return-type value)
  t)

(defstub logipedia-bool-match-true-elim
  (return-type case-true case-false boolean-value)
  t)

(defun-sk logipedia-bool-match-true-elim-typed-p ()
  (forall (return-type case-true case-false boolean-value)
    (implies
     (and
      (logipedia-bool-match-true-member-p
       return-type case-true)
      (logipedia-bool-match-true-member-p
       return-type case-false)
      (booleanp boolean-value))
     (logipedia-bool-match-true-member-p
      return-type
      (logipedia-bool-match-true-elim
       return-type case-true case-false boolean-value)))))

(defun-sk logipedia-bool-axiom-match-type-true-pointwise-p ()
  (forall (return-type case-true case-false)
    (implies
     (and
      (logipedia-bool-match-true-member-p
       return-type case-true)
      (logipedia-bool-match-true-member-p
       return-type case-false))
     (equal
      (logipedia-bool-match-true-elim
       return-type case-true case-false t)
      case-true))))

(defun logipedia-bool-axiom-match-type-true-statement ()
  (implies
   (logipedia-bool-match-true-elim-typed-p)
   (logipedia-bool-axiom-match-type-true-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
