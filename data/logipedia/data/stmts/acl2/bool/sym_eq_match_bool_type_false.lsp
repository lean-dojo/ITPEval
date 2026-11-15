;; Statement-only formalization of Logipedia corpus artifact
;; bool.sym_eq_match_bool_type_false, catalog title
;; "bool.sym_eq_match_bool_type_false": for every return type and two values
;; of that type, the false-branch value is Leibniz-equal to the polymorphic
;; Boolean eliminator applied to false. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source return types, abstract equality,
;; and polymorphic Boolean eliminator.

(defstub logipedia-bool-sym-eq-match-false-member-p
  (return-type value)
  t)

(defstub logipedia-bool-sym-eq-match-false-source-equal-p
  (return-type left right)
  t)

(defstub logipedia-bool-sym-eq-match-false-elim
  (return-type case-true case-false boolean-value)
  t)

(defun-sk logipedia-bool-sym-eq-match-false-elim-typed-p ()
  (forall (return-type case-true case-false boolean-value)
    (implies
     (and
      (logipedia-bool-sym-eq-match-false-member-p
       return-type case-true)
      (logipedia-bool-sym-eq-match-false-member-p
       return-type case-false)
      (booleanp boolean-value))
     (logipedia-bool-sym-eq-match-false-member-p
      return-type
      (logipedia-bool-sym-eq-match-false-elim
       return-type case-true case-false boolean-value)))))

(defun-sk logipedia-bool-sym-eq-match-false-equal-leibniz-p ()
  (forall (return-type left right)
    (implies
     (and
      (logipedia-bool-sym-eq-match-false-member-p return-type left)
      (logipedia-bool-sym-eq-match-false-member-p return-type right)
      (logipedia-bool-sym-eq-match-false-source-equal-p
       return-type left right))
     (equal left right))))

(defun-sk logipedia-bool-sym-eq-match-false-computation-p ()
  (forall (return-type case-true case-false)
    (implies
     (and
      (logipedia-bool-sym-eq-match-false-member-p
       return-type case-true)
      (logipedia-bool-sym-eq-match-false-member-p
       return-type case-false))
     (logipedia-bool-sym-eq-match-false-source-equal-p
      return-type
      (logipedia-bool-sym-eq-match-false-elim
       return-type case-true case-false nil)
      case-false))))

(defun-sk logipedia-bool-sym-eq-match-type-false-pointwise-p ()
  (forall (return-type case-true case-false)
    (implies
     (and
      (logipedia-bool-sym-eq-match-false-member-p
       return-type case-true)
      (logipedia-bool-sym-eq-match-false-member-p
       return-type case-false))
     (equal
      case-false
      (logipedia-bool-sym-eq-match-false-elim
       return-type case-true case-false nil)))))

(defun logipedia-bool-sym-eq-match-type-false-statement ()
  (implies
   (and
    (logipedia-bool-sym-eq-match-false-elim-typed-p)
    (logipedia-bool-sym-eq-match-false-equal-leibniz-p)
    (logipedia-bool-sym-eq-match-false-computation-p))
   (logipedia-bool-sym-eq-match-type-false-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
