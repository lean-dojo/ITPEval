;; Statement-only formalization of VERINA corpus artifact verina_advanced_60,
;; "partitionEvensOdds": a deterministic recursive traversal stably partitions
;; a list of natural numbers into its even and odd elements. This file
;; contains no proof.

(in-package "ACL2")

(defun verina-advanced-60-nat-listp (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (natp (car nums))
       (verina-advanced-60-nat-listp (cdr nums)))
    (equal nums nil)))

;; The source precondition is True. The List Nat binder is represented
;; separately in the final correctness predicate.

(defun verina-advanced-60-partition-evens-odds-precond (nums)
  (declare (ignore nums))
  t)

;; A Lean product of two lists is represented by the ACL2 cons pair
;; (evens . odds), with CAR and CDR as the two projections.

(defun verina-advanced-60-nat-list-pair-p (result)
  (and
   (consp result)
   (verina-advanced-60-nat-listp (car result))
   (verina-advanced-60-nat-listp (cdr result))))

;; This is the source local helper. It first partitions the tail, then
;; prepends the head to exactly one component, preserving order in both.

(defun verina-advanced-60-partition-helper (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (let ((tail-result
             (verina-advanced-60-partition-helper
              (cdr nums))))
        (if (equal (mod (car nums) 2) 0)
            (cons
             (cons (car nums) (car tail-result))
             (cdr tail-result))
          (cons
           (car tail-result)
           (cons (car nums) (cdr tail-result)))))
    (cons nil nil)))

;; The proof-valued True precondition argument is computationally irrelevant.

(defun verina-advanced-60-partition-evens-odds (nums)
  (verina-advanced-60-partition-helper nums))

(defun verina-advanced-60-filter-even (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (if (equal (mod (car nums) 2) 0)
          (cons
           (car nums)
           (verina-advanced-60-filter-even (cdr nums)))
        (verina-advanced-60-filter-even (cdr nums)))
    nil))

(defun verina-advanced-60-filter-odd (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (if (equal (mod (car nums) 2) 1)
          (cons
           (car nums)
           (verina-advanced-60-filter-odd (cdr nums)))
        (verina-advanced-60-filter-odd (cdr nums)))
    nil))

(defun verina-advanced-60-all-even-p (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (equal (mod (car nums) 2) 0)
       (verina-advanced-60-all-even-p (cdr nums)))
    (equal nums nil)))

(defun verina-advanced-60-all-odd-p (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (equal (mod (car nums) 2) 1)
       (verina-advanced-60-all-odd-p (cdr nums)))
    (equal nums nil)))

(defun verina-advanced-60-partition-evens-odds-postcond
    (nums result)
  (and
   (verina-advanced-60-nat-listp nums)
   (verina-advanced-60-nat-list-pair-p result)
   (equal
    (append (car result) (cdr result))
    (append
     (verina-advanced-60-filter-even nums)
     (verina-advanced-60-filter-odd nums)))
   (verina-advanced-60-all-even-p (car result))
   (verina-advanced-60-all-odd-p (cdr result))))

;; This predicate is the unproved final correctness proposition connecting
;; the complete precondition and postcondition to the exact executable result.

(defun
    verina-advanced-60-partition-evens-odds-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-60-nat-listp nums)
    (verina-advanced-60-partition-evens-odds-precond nums))
   (verina-advanced-60-partition-evens-odds-postcond
    nums
    (verina-advanced-60-partition-evens-odds nums))))

(value-triple :itpeval-statement-checked)
:q
