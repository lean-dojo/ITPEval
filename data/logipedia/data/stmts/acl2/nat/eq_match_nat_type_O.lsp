;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_match_nat_type_O, catalog title "nat.eq_match_nat_type_O":
;; for every return type, zero branch, and successor branch, the polymorphic
;; natural-number eliminator at zero is Leibniz-equal to the zero branch.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary return types, the source equality,
;; functions from naturals into those types, and the polymorphic eliminator.

(defstub logipedia-nat-eq-match-o-member-p
  (return-type value)
  t)

(defstub logipedia-nat-eq-match-o-source-equal-p
  (return-type left right)
  t)

(defstub logipedia-nat-eq-match-o-successor-at
  (successor-branch natural)
  t)

(defstub logipedia-nat-eq-match-o-elim
  (return-type zero-branch successor-branch natural)
  t)

(defun-sk logipedia-nat-eq-match-o-successor-typed-p
    (return-type successor-branch)
  (forall (natural)
    (implies
     (natp natural)
     (logipedia-nat-eq-match-o-member-p
      return-type
      (logipedia-nat-eq-match-o-successor-at
       successor-branch natural)))))

(defun-sk logipedia-nat-eq-match-o-elim-typed-p ()
  (forall (return-type zero-branch successor-branch natural)
    (implies
     (and
      (logipedia-nat-eq-match-o-member-p
       return-type zero-branch)
      (logipedia-nat-eq-match-o-successor-typed-p
       return-type successor-branch)
      (natp natural))
     (logipedia-nat-eq-match-o-member-p
      return-type
      (logipedia-nat-eq-match-o-elim
       return-type zero-branch successor-branch natural)))))

(defun-sk logipedia-nat-eq-match-o-equal-leibniz-p ()
  (forall (return-type left right)
    (implies
     (and
      (logipedia-nat-eq-match-o-member-p return-type left)
      (logipedia-nat-eq-match-o-member-p return-type right)
      (logipedia-nat-eq-match-o-source-equal-p
       return-type left right))
     (equal left right))))

(defun-sk logipedia-nat-eq-match-o-computation-p ()
  (forall (return-type zero-branch successor-branch)
    (implies
     (and
      (logipedia-nat-eq-match-o-member-p
       return-type zero-branch)
      (logipedia-nat-eq-match-o-successor-typed-p
       return-type successor-branch))
     (logipedia-nat-eq-match-o-source-equal-p
      return-type
      (logipedia-nat-eq-match-o-elim
       return-type zero-branch successor-branch 0)
      zero-branch))))

(defun-sk logipedia-nat-eq-match-type-o-pointwise-p ()
  (forall (return-type zero-branch successor-branch)
    (implies
     (and
      (logipedia-nat-eq-match-o-member-p
       return-type zero-branch)
      (logipedia-nat-eq-match-o-successor-typed-p
       return-type successor-branch))
     (equal
      (logipedia-nat-eq-match-o-elim
       return-type zero-branch successor-branch 0)
      zero-branch))))

(defun logipedia-nat-eq-match-type-o-statement ()
  (implies
   (and
    (logipedia-nat-eq-match-o-elim-typed-p)
    (logipedia-nat-eq-match-o-equal-leibniz-p)
    (logipedia-nat-eq-match-o-computation-p))
   (logipedia-nat-eq-match-type-o-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
