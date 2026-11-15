;; Statement-only formalization of Logipedia corpus artifact
;; bool.eq_match_bool_type_false, catalog title
;; "bool.eq_match_bool_type_false": for every return type and two values
;; of that type, the polymorphic Boolean eliminator applied to false is
;; Leibniz-equal to its false-branch value. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source return types, abstract equality,
;; and polymorphic Boolean eliminator.

(defstub logipedia-bool-eq-match-false-member-p
  (return-type value)
  t)

(defstub logipedia-bool-eq-match-false-source-equal-p
  (return-type left right)
  t)

(defstub logipedia-bool-eq-match-false-elim
  (return-type case-true case-false boolean-value)
  t)

(defun-sk logipedia-bool-eq-match-false-elim-typed-p ()
  (forall (return-type case-true case-false boolean-value)
    (implies
     (and
      (logipedia-bool-eq-match-false-member-p
       return-type case-true)
      (logipedia-bool-eq-match-false-member-p
       return-type case-false)
      (booleanp boolean-value))
     (logipedia-bool-eq-match-false-member-p
      return-type
      (logipedia-bool-eq-match-false-elim
       return-type case-true case-false boolean-value)))))

(defun-sk logipedia-bool-eq-match-false-equal-leibniz-p ()
  (forall (return-type left right)
    (implies
     (and
      (logipedia-bool-eq-match-false-member-p return-type left)
      (logipedia-bool-eq-match-false-member-p return-type right)
      (logipedia-bool-eq-match-false-source-equal-p
       return-type left right))
     (equal left right))))

(defun-sk logipedia-bool-eq-match-false-computation-p ()
  (forall (return-type case-true case-false)
    (implies
     (and
      (logipedia-bool-eq-match-false-member-p
       return-type case-true)
      (logipedia-bool-eq-match-false-member-p
       return-type case-false))
     (logipedia-bool-eq-match-false-source-equal-p
      return-type
      (logipedia-bool-eq-match-false-elim
       return-type case-true case-false nil)
      case-false))))

(defun-sk logipedia-bool-eq-match-type-false-pointwise-p ()
  (forall (return-type case-true case-false)
    (implies
     (and
      (logipedia-bool-eq-match-false-member-p
       return-type case-true)
      (logipedia-bool-eq-match-false-member-p
       return-type case-false))
     (equal
      (logipedia-bool-eq-match-false-elim
       return-type case-true case-false nil)
      case-false))))

(defun logipedia-bool-eq-match-type-false-statement ()
  (implies
   (and
    (logipedia-bool-eq-match-false-elim-typed-p)
    (logipedia-bool-eq-match-false-equal-leibniz-p)
    (logipedia-bool-eq-match-false-computation-p))
   (logipedia-bool-eq-match-type-false-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
