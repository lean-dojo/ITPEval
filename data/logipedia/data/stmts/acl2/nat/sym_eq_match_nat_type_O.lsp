;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_match_nat_type_O, catalog title "nat.sym_eq_match_nat_type_O":
;; for every return type, zero branch, and successor branch, the zero branch
;; is Leibniz-equal to the polymorphic natural-number eliminator at zero.
;; This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary return types, the source equality,
;; functions from naturals into those types, and the polymorphic eliminator.

(defstub logipedia-nat-sym-match-o-member-p
  (return-type value)
  t)

(defstub logipedia-nat-sym-match-o-source-equal-p
  (return-type left right)
  t)

(defstub logipedia-nat-sym-match-o-successor-at
  (successor-branch natural)
  t)

(defstub logipedia-nat-sym-match-o-elim
  (return-type zero-branch successor-branch natural)
  t)

(defun-sk logipedia-nat-sym-match-o-successor-typed-p
    (return-type successor-branch)
  (forall (natural)
    (implies
     (natp natural)
     (logipedia-nat-sym-match-o-member-p
      return-type
      (logipedia-nat-sym-match-o-successor-at
       successor-branch natural)))))

(defun-sk logipedia-nat-sym-match-o-elim-typed-p ()
  (forall (return-type zero-branch successor-branch natural)
    (implies
     (and
      (logipedia-nat-sym-match-o-member-p
       return-type zero-branch)
      (logipedia-nat-sym-match-o-successor-typed-p
       return-type successor-branch)
      (natp natural))
     (logipedia-nat-sym-match-o-member-p
      return-type
      (logipedia-nat-sym-match-o-elim
       return-type zero-branch successor-branch natural)))))

(defun-sk logipedia-nat-sym-match-o-equal-leibniz-p ()
  (forall (return-type left right)
    (implies
     (and
      (logipedia-nat-sym-match-o-member-p return-type left)
      (logipedia-nat-sym-match-o-member-p return-type right)
      (logipedia-nat-sym-match-o-source-equal-p
       return-type left right))
     (equal left right))))

(defun-sk logipedia-nat-sym-match-o-computation-p ()
  (forall (return-type zero-branch successor-branch)
    (implies
     (and
      (logipedia-nat-sym-match-o-member-p
       return-type zero-branch)
      (logipedia-nat-sym-match-o-successor-typed-p
       return-type successor-branch))
     (logipedia-nat-sym-match-o-source-equal-p
      return-type
      (logipedia-nat-sym-match-o-elim
       return-type zero-branch successor-branch 0)
      zero-branch))))

;; Leibniz equality is equivalent to identity: identity transports every
;; predicate, and the converse uses the predicate z |-> (z = left).

(defun-sk logipedia-nat-sym-match-type-o-pointwise-p ()
  (forall (return-type zero-branch successor-branch)
    (implies
     (and
      (logipedia-nat-sym-match-o-member-p
       return-type zero-branch)
      (logipedia-nat-sym-match-o-successor-typed-p
       return-type successor-branch))
     (equal
      zero-branch
      (logipedia-nat-sym-match-o-elim
       return-type zero-branch successor-branch 0)))))

(defun logipedia-nat-sym-match-type-o-statement ()
  (implies
   (and
    (logipedia-nat-sym-match-o-elim-typed-p)
    (logipedia-nat-sym-match-o-equal-leibniz-p)
    (logipedia-nat-sym-match-o-computation-p))
   (logipedia-nat-sym-match-type-o-pointwise-p)))

(value-triple :itpeval-statement-checked)
:q
