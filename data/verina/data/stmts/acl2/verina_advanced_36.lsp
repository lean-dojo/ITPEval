;; Statement-only formalization of VERINA corpus artifact verina_advanced_36,
;; "majorityElement": a deterministic Boyer-Moore candidate scan on a
;; nonempty list of natural numbers returns an element occurring strictly more
;; than half the list length. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-36-nat-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (natp (car xs))
       (verina-advanced-36-nat-listp (cdr xs)))
    (equal xs nil)))

;; This is the source local countOccurrences helper. It is retained even
;; though the executable candidate scan does not call it.

(defun verina-advanced-36-count-occurrences (target lst)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (+
       (if (equal (car lst) target) 1 0)
       (verina-advanced-36-count-occurrences
        target
        (cdr lst)))
    0))

;; This predicate is List.any applied to the strict-majority test.

(defun verina-advanced-36-any-majority-p
    (remaining whole threshold)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (or
       (< threshold
          (verina-advanced-36-count-occurrences
           (car remaining)
           whole))
       (verina-advanced-36-any-majority-p
        (cdr remaining)
        whole
        threshold))
    nil))

(defun verina-advanced-36-majority-element-precond (xs)
  (and
   (< 0 (len xs))
   (verina-advanced-36-any-majority-p
    xs
    xs
    (floor (len xs) 2))))

;; CANDIDATE-PRESENTP and CANDIDATE represent Option Nat exactly on reachable
;; calls: NIL is none, and non-NIL is some CANDIDATE. COUNT is the source Nat
;; counter. NFIX implements truncated Nat subtraction in the decrement branch.

(defun verina-advanced-36-find-candidate
    (lst candidate-presentp candidate count)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (let ((x (car lst))
            (tail (cdr lst)))
        (if candidate-presentp
            (if (equal x candidate)
                (verina-advanced-36-find-candidate
                 tail
                 t
                 candidate
                 (+ count 1))
              (if (equal count 0)
                  (verina-advanced-36-find-candidate
                   tail
                   t
                   x
                   1)
                (verina-advanced-36-find-candidate
                 tail
                 t
                 candidate
                 (nfix (- count 1)))))
          (verina-advanced-36-find-candidate
           tail
           t
           x
           1)))
    (if candidate-presentp candidate 0)))

;; The proof-valued precondition argument is computationally irrelevant, so
;; this function is the exact executable content of the source definition.

(defun verina-advanced-36-majority-element (xs)
  (verina-advanced-36-find-candidate xs nil 0 0))

(defun verina-advanced-36-majority-element-postcond
    (xs result)
  (and
   (verina-advanced-36-nat-listp xs)
   (natp result)
   (< (floor (len xs) 2)
      (verina-advanced-36-count-occurrences
       result
       xs))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Nat binder and complete source precondition;
;; its conclusion applies the postcondition to the exact executable result.

(defun verina-advanced-36-majority-element-spec-satisfied-statement
    (xs)
  (implies
   (and
    (verina-advanced-36-nat-listp xs)
    (verina-advanced-36-majority-element-precond xs))
   (verina-advanced-36-majority-element-postcond
    xs
    (verina-advanced-36-majority-element xs))))

(value-triple :itpeval-statement-checked)
:q
