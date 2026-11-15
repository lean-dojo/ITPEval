;; Statement-only formalization of VERINA corpus artifact verina_advanced_64,
;; "removeElement": a deterministic recursive program removes every occurrence
;; of a target natural number from a list while preserving the order of all
;; remaining elements. This file contains no proof.

(in-package "ACL2")

;; Lean's List Nat domain is represented by proper ACL2 lists of naturals.

(defun verina-advanced-64-nat-listp (lst)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (and
       (natp (car lst))
       (verina-advanced-64-nat-listp (cdr lst)))
    (equal lst nil)))

;; The source precondition is True. The typed input domains are represented
;; explicitly in the final correctness predicate.

(defun verina-advanced-64-remove-element-precond
    (lst target)
  (declare (ignore lst target))
  t)

;; This is the source-local helper. It recursively processes the tail first,
;; then omits the head exactly when it equals TARGET.

(defun verina-advanced-64-remove-element-helper
    (lst target)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (let ((rest
             (verina-advanced-64-remove-element-helper
              (cdr lst)
              target)))
        (if (equal (car lst) target)
            rest
          (cons (car lst) rest)))
    nil))

;; The proof-valued True precondition argument is computationally irrelevant,
;; so this wrapper is exactly the executable content of the source definition.

(defun verina-advanced-64-remove-element
    (lst target)
  (verina-advanced-64-remove-element-helper lst target))

;; This recursion is the source List.filter (fun x => x != target).

(defun verina-advanced-64-filter-not-target
    (lst target)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (if (equal (car lst) target)
          (verina-advanced-64-filter-not-target
           (cdr lst)
           target)
        (cons
         (car lst)
         (verina-advanced-64-filter-not-target
          (cdr lst)
          target)))
    nil))

;; Option Nat is represented by :none or the tagged pair (:some . value).
;; This is List.get? at a natural index.

(defun verina-advanced-64-nth-option
    (index values)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      :none
    (if (consp values)
        (if (zp index)
            (cons :some (car values))
          (verina-advanced-64-nth-option
           (- index 1)
           (cdr values)))
      :none)))

;; Starting at INDEX, this is result.zipIdx.all applied to the source match
;; against the corresponding optional entry of the filtered input.

(defun verina-advanced-64-all-indexed-entries-match-p
    (result filtered index)
  (declare (xargs :measure (acl2-count result)))
  (if (consp result)
      (and
       (equal
        (verina-advanced-64-nth-option
         index
         filtered)
        (cons :some (car result)))
       (verina-advanced-64-all-indexed-entries-match-p
        (cdr result)
        filtered
        (+ index 1)))
    t))

;; The source proof argument is unused here. The indexed comparison and equal
;; length jointly state that RESULT is exactly the filtered list, in order.

(defun verina-advanced-64-remove-element-postcond
    (lst target result)
  (let ((filtered
         (verina-advanced-64-filter-not-target
          lst
          target)))
    (and
     (verina-advanced-64-nat-listp lst)
     (natp target)
     (verina-advanced-64-nat-listp result)
     (verina-advanced-64-all-indexed-entries-match-p
      result
      filtered
      0)
     (equal (len result) (len filtered)))))

;; This predicate is the unproved final correctness proposition connecting
;; the complete precondition and postcondition to the exact executable result.

(defun
    verina-advanced-64-remove-element-spec-satisfied-statement
    (lst target)
  (implies
   (and
    (verina-advanced-64-nat-listp lst)
    (natp target)
    (verina-advanced-64-remove-element-precond
     lst
     target))
   (verina-advanced-64-remove-element-postcond
    lst
    target
    (verina-advanced-64-remove-element lst target))))

(value-triple :itpeval-statement-checked)
:q
