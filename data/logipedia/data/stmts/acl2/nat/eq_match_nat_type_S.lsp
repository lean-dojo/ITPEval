;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_match_nat_type_S, catalog title "nat.eq_match_nat_type_S":
;; for every return type, zero branch, successor branch, and natural number,
;; the polymorphic natural-number eliminator at that number's successor is
;; Leibniz-equal to the successor branch applied to the number. This file
;; contains no proof.

(in-package "ACL2")

;; Conservative interfaces reify arbitrary return types, functions from
;; naturals into those types, and the polymorphic eliminator.

(defstub logipedia-nat-eq-match-s-member-p
  (return-type value)
  t)

(defstub logipedia-nat-eq-match-s-successor-at
  (successor-branch natural)
  t)

(defstub logipedia-nat-eq-match-s-elim
  (return-type zero-branch successor-branch natural)
  t)

(defun-sk logipedia-nat-eq-match-s-successor-typed-p
    (return-type successor-branch)
  (forall (natural)
    (implies
     (natp natural)
     (logipedia-nat-eq-match-s-member-p
      return-type
      (logipedia-nat-eq-match-s-successor-at
       successor-branch natural)))))

;; Leibniz equality, forall P, P(x) -> P(y), is equivalent to identity:
;; identity transports every predicate, and the converse uses P(z) = (z = x).

(defun-sk logipedia-nat-eq-match-type-s-pointwise-p ()
  (forall (return-type zero-branch successor-branch natural)
    (implies
     (and
      (logipedia-nat-eq-match-s-member-p
       return-type zero-branch)
      (logipedia-nat-eq-match-s-successor-typed-p
       return-type successor-branch)
      (natp natural))
     (equal
      (logipedia-nat-eq-match-s-elim
       return-type zero-branch successor-branch (+ natural 1))
      (logipedia-nat-eq-match-s-successor-at
       successor-branch natural)))))

(defun logipedia-nat-eq-match-type-s-statement ()
  (logipedia-nat-eq-match-type-s-pointwise-p))

(value-triple :itpeval-statement-checked)
:q
