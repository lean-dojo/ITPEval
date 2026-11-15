;; Statement-only formalization of PutnamBench corpus artifact putnam_1989_b4:
;; there exists an uncountable collection of nonempty subsets of a countably
;; infinite set such that distinct members have finite intersection. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The natural numbers are the canonical countably infinite carrier. Subsets
;; and their family are tame APPLY$ predicates, with explicit extensionality.
;; DEFUN-SK keeps the family and all auxiliary witnesses internally quantified.
;; Countability is existence of an extensional injection into the naturals.
;; A subset of the naturals is finite exactly when it has a natural bound.

(defun putnam-1989-b4-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun putnam-1989-b4-value (function object)
  (apply$ function (list object)))

(defun-sk putnam-1989-b4-members-are-natural-p (set)
  (forall (object)
    (implies
     (putnam-1989-b4-member-p set object)
     (natp object))))

(defun putnam-1989-b4-nat-set-p (set)
  (and
   (tamep-functionp set)
   (putnam-1989-b4-members-are-natural-p set)))

(defun-sk putnam-1989-b4-nat-set-equiv-p (left right)
  (forall (n)
    (implies
     (natp n)
     (iff
      (putnam-1989-b4-member-p left n)
      (putnam-1989-b4-member-p right n)))))

(defun-sk putnam-1989-b4-family-members-valid-p (family)
  (forall (set)
    (implies
     (putnam-1989-b4-member-p family set)
     (putnam-1989-b4-nat-set-p set))))

(defun-sk putnam-1989-b4-family-extensional-p (family)
  (forall (left right)
    (implies
     (and
      (putnam-1989-b4-nat-set-p left)
      (putnam-1989-b4-nat-set-p right)
      (putnam-1989-b4-nat-set-equiv-p left right))
     (iff
      (putnam-1989-b4-member-p family left)
      (putnam-1989-b4-member-p family right)))))

(defun putnam-1989-b4-family-of-nat-sets-p (family)
  (and
   (tamep-functionp family)
   (putnam-1989-b4-family-members-valid-p family)
   (putnam-1989-b4-family-extensional-p family)))

(defun-sk putnam-1989-b4-nat-set-nonempty-p (set)
  (exists (n)
    (and
     (natp n)
     (putnam-1989-b4-member-p set n))))

(defun-sk putnam-1989-b4-all-members-nonempty-p (family)
  (forall (set)
    (implies
     (putnam-1989-b4-member-p family set)
     (putnam-1989-b4-nat-set-nonempty-p set))))

(defun-sk putnam-1989-b4-intersection-bounded-p
    (left right bound)
  (forall (n)
    (implies
     (and
      (natp n)
      (putnam-1989-b4-member-p left n)
      (putnam-1989-b4-member-p right n))
     (< n bound))))

(defun-sk putnam-1989-b4-intersection-finite-p (left right)
  (exists (bound)
    (and
     (natp bound)
     (putnam-1989-b4-intersection-bounded-p
      left right bound))))

(defun-sk putnam-1989-b4-pairwise-finite-intersections-p (family)
  (forall (left right)
    (implies
     (and
      (putnam-1989-b4-member-p family left)
      (putnam-1989-b4-member-p family right)
      (not
       (putnam-1989-b4-nat-set-equiv-p left right)))
     (putnam-1989-b4-intersection-finite-p left right))))

;; An encoding represents a function on extensional subsets: it is invariant
;; under set equivalence, maps family members to naturals, and is injective on
;; the family modulo extensional equality.

(defun-sk putnam-1989-b4-countable-encoding-laws-p
    (family encoding)
  (forall (left right)
    (and
     (implies
      (putnam-1989-b4-member-p family left)
      (natp
       (putnam-1989-b4-value encoding left)))
     (implies
      (and
       (putnam-1989-b4-member-p family left)
       (putnam-1989-b4-member-p family right)
       (putnam-1989-b4-nat-set-equiv-p left right))
      (equal
       (putnam-1989-b4-value encoding left)
       (putnam-1989-b4-value encoding right)))
     (implies
      (and
       (putnam-1989-b4-member-p family left)
       (putnam-1989-b4-member-p family right)
       (equal
        (putnam-1989-b4-value encoding left)
        (putnam-1989-b4-value encoding right)))
      (putnam-1989-b4-nat-set-equiv-p left right)))))

(defun putnam-1989-b4-countable-encoding-p
    (family encoding)
  (and
   (tamep-functionp encoding)
   (putnam-1989-b4-countable-encoding-laws-p
    family encoding)))

(defun-sk putnam-1989-b4-family-countable-p (family)
  (exists (encoding)
    (putnam-1989-b4-countable-encoding-p
     family encoding)))

(defun-sk putnambench-putnam-1989-b4-statement ()
  (exists (family)
    (and
     (putnam-1989-b4-family-of-nat-sets-p family)
     (not
      (putnam-1989-b4-family-countable-p family))
     (putnam-1989-b4-all-members-nonempty-p family)
     (putnam-1989-b4-pairwise-finite-intersections-p
      family))))

(value-triple :itpeval-statement-checked)
:q
