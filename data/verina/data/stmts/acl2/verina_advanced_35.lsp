;; Statement-only formalization of VERINA corpus artifact verina_advanced_35,
;; "majorityElement": a deterministic integer-counting map computation returns
;; the unique list element occurring strictly more than half the list length,
;; together with its majority-element correctness contract. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-35-integer-listp (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (integerp (car nums))
       (verina-advanced-35-integer-listp (cdr nums)))
    (equal nums nil)))

(defun verina-advanced-35-count-occurrences (value nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (+
       (if (equal value (car nums)) 1 0)
       (verina-advanced-35-count-occurrences
        value
        (cdr nums)))
    0))

;; This predicate is List.any applied to the strict-majority test.

(defun verina-advanced-35-any-majority-p
    (remaining whole threshold)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (or
       (< threshold
          (verina-advanced-35-count-occurrences
           (car remaining)
           whole))
       (verina-advanced-35-any-majority-p
        (cdr remaining)
        whole
        threshold))
    nil))

(defun verina-advanced-35-majority-element-precond (nums)
  (and
   (< 0 (len nums))
   (verina-advanced-35-any-majority-p
    nums
    nums
    (floor (len nums) 2))))

;; The source HashMap Int Nat is represented extensionally by a proper list of
;; dotted pairs (key . count), with one entry per encountered integer key.

(defun verina-advanced-35-map-getd (key counts default)
  (declare (xargs :measure (acl2-count counts)))
  (if (consp counts)
      (if (equal key (car (car counts)))
          (cdr (car counts))
        (verina-advanced-35-map-getd
         key
         (cdr counts)
         default))
    default))

(defun verina-advanced-35-map-insert (key value counts)
  (declare (xargs :measure (acl2-count counts)))
  (if (consp counts)
      (if (equal key (car (car counts)))
          (cons
           (cons key value)
           (cdr counts))
        (cons
         (car counts)
         (verina-advanced-35-map-insert
          key
          value
          (cdr counts))))
    (list (cons key value))))

;; This recursion is the source for-loop. At each element it performs getD
;; with default zero and reinserts the incremented natural count.

(defun verina-advanced-35-build-counts (remaining counts)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((key (car remaining))
             (count
              (verina-advanced-35-map-getd
               key
               counts
               0))
             (next-counts
              (verina-advanced-35-map-insert
               key
               (+ count 1)
               counts)))
        (verina-advanced-35-build-counts
         (cdr remaining)
         next-counts))
    counts))

;; This is counts.toList.find? followed by the source match. A strict majority
;; key is unique, so the finite-map enumeration order cannot affect the result.

(defun verina-advanced-35-find-majority-entry
    (counts threshold)
  (declare (xargs :measure (acl2-count counts)))
  (if (consp counts)
      (if (< threshold (cdr (car counts)))
          (car (car counts))
        (verina-advanced-35-find-majority-entry
         (cdr counts)
         threshold))
    0))

;; The proof-valued precondition argument is computationally irrelevant.

(defun verina-advanced-35-majority-element (nums)
  (let* ((counts
          (verina-advanced-35-build-counts nums nil))
         (n (len nums)))
    (verina-advanced-35-find-majority-entry
     counts
     (floor n 2))))

;; This recursive predicate is the source universal quantifier
;; forall x in nums, x != result -> count x <= floor(n/2).

(defun verina-advanced-35-all-other-counts-at-most-p
    (remaining whole result threshold)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (implies
        (not (equal (car remaining) result))
        (<=
         (verina-advanced-35-count-occurrences
          (car remaining)
          whole)
         threshold))
       (verina-advanced-35-all-other-counts-at-most-p
        (cdr remaining)
        whole
        result
        threshold))
    (equal remaining nil)))

(defun verina-advanced-35-majority-element-postcond
    (nums result)
  (let ((threshold (floor (len nums) 2)))
    (and
     (verina-advanced-35-integer-listp nums)
     (integerp result)
     (< threshold
        (verina-advanced-35-count-occurrences
         result
         nums))
     (verina-advanced-35-all-other-counts-at-most-p
      nums
      nums
      result
      threshold))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and complete source precondition;
;; its conclusion applies the complete postcondition to the executable result.

(defun verina-advanced-35-majority-element-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-35-integer-listp nums)
    (verina-advanced-35-majority-element-precond nums))
   (verina-advanced-35-majority-element-postcond
    nums
    (verina-advanced-35-majority-element nums))))

(value-triple :itpeval-statement-checked)
:q
