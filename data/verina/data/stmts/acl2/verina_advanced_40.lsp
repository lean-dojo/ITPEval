;; Statement-only formalization of VERINA corpus artifact verina_advanced_40,
;; "maxOfList": the recursive program returns a member of a nonempty list of
;; natural numbers that is at least every element. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-40-nat-listp (lst)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (and
       (natp (car lst))
       (verina-advanced-40-nat-listp (cdr lst)))
    (equal lst nil)))

(defun verina-advanced-40-max-of-list-precond (lst)
  (not (equal lst nil)))

;; This is the source local helper: the empty branch returns zero, the
;; singleton branch returns its element, and a longer list compares its head
;; with the recursively computed maximum of its tail.

(defun verina-advanced-40-max-of-list-helper (lst)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (if (consp (cdr lst))
          (let ((max-tail
                 (verina-advanced-40-max-of-list-helper
                  (cdr lst))))
            (if (> (car lst) max-tail)
                (car lst)
              max-tail))
        (car lst))
    0))

;; The proof-valued precondition argument is computationally irrelevant, so
;; this wrapper is exactly the executable content of the source definition.

(defun verina-advanced-40-max-of-list (lst)
  (verina-advanced-40-max-of-list-helper lst))

;; This recursion is the bounded universal quantifier over list membership in
;; the source postcondition.

(defun verina-advanced-40-all-elements-at-most-p
    (lst result)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (and
       (<= (car lst) result)
       (verina-advanced-40-all-elements-at-most-p
        (cdr lst)
        result))
    t))

(defun verina-advanced-40-max-of-list-postcond
    (lst result)
  (and
   (verina-advanced-40-nat-listp lst)
   (natp result)
   (member-equal result lst)
   (verina-advanced-40-all-elements-at-most-p
    lst
    result)))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Nat binder and nonempty-list precondition;
;; its conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-40-max-of-list-spec-satisfied-statement
    (lst)
  (implies
   (and
    (verina-advanced-40-nat-listp lst)
    (verina-advanced-40-max-of-list-precond lst))
   (verina-advanced-40-max-of-list-postcond
    lst
    (verina-advanced-40-max-of-list lst))))

(value-triple :itpeval-statement-checked)
:q
