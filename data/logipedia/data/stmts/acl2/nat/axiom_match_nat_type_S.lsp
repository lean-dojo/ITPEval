;; Statement-only formalization of Logipedia corpus artifact
;; nat.axiom_match_nat_type_S, catalog title
;; "nat.axiom_match_nat_type_S": for every return type, zero branch,
;; successor branch, and natural number, the polymorphic natural-number
;; eliminator at that number's successor is related by the source equality
;; to the successor branch applied to the number. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary return types, the source equality,
;; functions from naturals into those types, and the polymorphic eliminator.

(defstub logipedia-nat-match-s-member-p
  (return-type value)
  t)

(defstub logipedia-nat-match-s-source-equal-p
  (return-type left right)
  t)

(defstub logipedia-nat-match-s-successor-at
  (return-type successor-branch natural)
  t)

(defstub logipedia-nat-match-s-elim
  (return-type zero-branch successor-branch natural)
  t)

(defun-sk logipedia-nat-match-s-successor-typed-p
    (return-type successor-branch)
  (forall (natural)
    (implies
     (natp natural)
     (logipedia-nat-match-s-member-p
      return-type
      (logipedia-nat-match-s-successor-at
       return-type successor-branch natural)))))

(defun-sk logipedia-nat-axiom-match-type-s-pointwise-p ()
  (forall (return-type zero-branch successor-branch natural)
    (implies
     (and
      (logipedia-nat-match-s-member-p
       return-type zero-branch)
      (logipedia-nat-match-s-successor-typed-p
       return-type successor-branch)
      (natp natural))
     (logipedia-nat-match-s-source-equal-p
      return-type
      (logipedia-nat-match-s-elim
       return-type zero-branch successor-branch (+ natural 1))
      (logipedia-nat-match-s-successor-at
       return-type successor-branch natural)))))

(defun logipedia-nat-axiom-match-type-s-statement ()
  (logipedia-nat-axiom-match-type-s-pointwise-p))

(value-triple :itpeval-statement-checked)
:q
