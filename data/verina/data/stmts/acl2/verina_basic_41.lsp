;; Statement-only formalization of VERINA corpus artifact verina_basic_41,
;; catalog title "hasOnlyOneDistinctElement": a deterministic program on a
;; nonempty integer array returns true exactly when all entries are equal.
;; This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-41-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-41-int-array-p (cdr a)))
    (equal a nil)))

;; Array.size > 0 is exactly nonemptiness for the list representation.

(defun verina-basic-41-has-only-one-distinct-element-precond (a)
  (consp a))

;; REMAINING is the suffix beginning at the source loop index. This structural
;; recursion returns false at the first entry unequal to FIRST and true after
;; exhausting the suffix, exactly as the indexed Lean loop does.

(defun verina-basic-41-all-equal-to-p (remaining first)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (equal (car remaining) first)
       (verina-basic-41-all-equal-to-p
        (cdr remaining)
        first))
    t))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. The empty branch returns true; otherwise the exact source scan
;; starts at index one and compares every remaining entry with index zero.

(defun verina-basic-41-has-only-one-distinct-element (a)
  (if (consp a)
      (verina-basic-41-all-equal-to-p
       (cdr a)
       (car a))
    t))

(defun verina-basic-41-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; List.Pairwise equality requires each head to equal every later element and
;; recursively imposes the same requirement on the tail.

(defun verina-basic-41-head-equal-to-all-p (first remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (equal first (car remaining))
       (verina-basic-41-head-equal-to-all-p
        first
        (cdr remaining)))
    t))

(defun verina-basic-41-pairwise-equal-p (values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (and
       (verina-basic-41-head-equal-to-all-p
        (car values)
        (cdr values))
       (verina-basic-41-pairwise-equal-p
        (cdr values)))
    (equal values nil)))

;; Array/List get! at index zero returns the first integer when present and
;; the inhabited integer default zero on an empty list.

(defun verina-basic-41-first-default-zero (values)
  (if (consp values)
      (car values)
    0))

;; This recursion is exactly l.any (fun x => x != l[0]!).

(defun verina-basic-41-any-different-from-p
    (values reference)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (or
       (not (equal (car values) reference))
       (verina-basic-41-any-different-from-p
        (cdr values)
        reference))
    nil))

;; This is the complete source postcondition. ACL2 t/nil are the two Boolean
;; values, so its implications reproduce the source Bool-to-Prop coercions.
;; The unused proof-valued precondition argument is erased.

(defun verina-basic-41-has-only-one-distinct-element-postcond
    (a result)
  (and
   (verina-basic-41-int-array-p a)
   (verina-basic-41-bool-p result)
   (implies
    result
    (verina-basic-41-pairwise-equal-p a))
   (implies
    (not result)
    (verina-basic-41-any-different-from-p
     a
     (verina-basic-41-first-default-zero a)))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array, applies the exact nonempty precondition,
;; and connects the complete postcondition to the executable result.

(defun-sk
    verina-basic-41-has-only-one-distinct-element-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-41-int-array-p a)
      (verina-basic-41-has-only-one-distinct-element-precond a))
     (verina-basic-41-has-only-one-distinct-element-postcond
      a
      (verina-basic-41-has-only-one-distinct-element a)))))

(value-triple :itpeval-statement-checked)
:q
