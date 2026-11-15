;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_match_nat_type_O, catalog title
;; "nat.axiom_match_nat_type_O": for every return type, zero branch, and
;; successor branch, the polymorphic natural-number eliminator at zero is
;; related to the zero branch by the source equality. This file contains no
;; proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary return types, the source equality,
;; functions from naturals into those types, and the polymorphic eliminator.

(defstub logipedia-nat-match-o-member-p
  (return-type value)
  t)

(defstub logipedia-nat-match-o-source-equal-p
  (return-type left right)
  t)

(defstub logipedia-nat-match-o-successor-at
  (return-type successor-branch natural)
  t)

(defstub logipedia-nat-match-o-elim
  (return-type zero-branch successor-branch natural)
  t)

(defun-sk logipedia-nat-match-o-successor-typed-p
    (return-type successor-branch)
  (forall (natural)
    (implies
     (natp natural)
     (logipedia-nat-match-o-member-p
      return-type
      (logipedia-nat-match-o-successor-at
       return-type successor-branch natural)))))

(defun-sk logipedia-nat-axiom-match-type-o-pointwise-p ()
  (forall (return-type zero-branch successor-branch)
    (implies
     (and
      (logipedia-nat-match-o-member-p
       return-type zero-branch)
      (logipedia-nat-match-o-successor-typed-p
       return-type successor-branch))
     (logipedia-nat-match-o-source-equal-p
      return-type
      (logipedia-nat-match-o-elim
       return-type zero-branch successor-branch 0)
      zero-branch))))

(defun logipedia-nat-axiom-match-type-o-statement ()
  (logipedia-nat-axiom-match-type-o-pointwise-p))

(value-triple :itpeval-statement-checked)
:q
