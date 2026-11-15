;; Statement-only formalization of Logipedia corpus artifact
;; bool.eq_match_bool_type_true, catalog title
;; "bool.eq_match_bool_type_true": for every return type and two values
;; of that type, the polymorphic Boolean eliminator applied to true is
;; Leibniz-equal to its true-branch value. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces for the source return types, abstract equality,
;; and polymorphic Boolean eliminator.

(defstub logipedia-bool-eq-match-true-member-p
  (return-type value)
  t)

(defstub logipedia-bool-eq-match-true-source-equal-p
  (return-type left right)
  t)

(defstub logipedia-bool-eq-match-true-elim
  (return-type case-true case-false boolean-value)
  t)

(defun-sk logipedia-bool-eq-match-true-elim-typed-p ()
  (forall (return-type case-true case-false boolean-value)
    (implies
     (and
      (logipedia-bool-eq-match-true-member-p
       return-type case-true)
      (logipedia-bool-eq-match-true-member-p
       return-type case-false)
      (booleanp boolean-value))
     (logipedia-bool-eq-match-true-member-p
      return-type
      (logipedia-bool-eq-match-true-elim
       return-type case-true case-false boolean-value)))))

(defun-sk logipedia-bool-eq-match-true-equal-leibniz-p ()
  (forall (return-type left right)
    (implies
     (and
      (logipedia-bool-eq-match-true-member-p return-type left)
      (logipedia-bool-eq-match-true-member-p return-type right)
      (logipedia-bool-eq-match-true-source-equal-p
       return-type left right))
     (equal left right))))

(defun-sk logipedia-bool-eq-match-true-computation-p ()
  (forall (return-type case-true case-false)
    (implies
     (and
      (logipedia-bool-eq-match-true-member-p
       return-type case-true)
      (logipedia-bool-eq-match-true-member-p
       return-type case-false))
     (logipedia-bool-eq-match-true-source-equal-p
      return-type
      (logipedia-bool-eq-match-true-elim
       return-type case-true case-false t)
      case-true))))

(defun-sk logipedia-bool-eq-match-type-true-pointwise-p ()
  (forall (return-type case-true case-false)
    (implies
     (and
      (logipedia-bool-eq-match-true-member-p
       return-type case-true)
      (logipedia-bool-eq-match-true-member-p
       return-type case-false))
     (equal
      (logipedia-bool-eq-match-true-elim
       return-type case-true case-false t)
      case-true))))

(defun logipedia-bool-eq-match-type-true-statement ()
  (implies
   (and
    (logipedia-bool-eq-match-true-elim-typed-p)
    (logipedia-bool-eq-match-true-equal-leibniz-p)
    (logipedia-bool-eq-match-true-computation-p))
   (logipedia-bool-eq-match-type-true-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
