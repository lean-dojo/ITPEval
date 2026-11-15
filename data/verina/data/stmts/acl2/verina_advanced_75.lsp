;; Statement-only formalization of VERINA corpus artifact verina_advanced_75,
;; "task_code": the deterministic Kadane-style integer-list program returns
;; the greatest sum of a nonempty contiguous subarray of a nonempty input
;; sequence, with its full correctness contract. This file contains no proof.

(in-package "ACL2")

;; Lean's List Int domain is represented by proper ACL2 lists of integers.

(defun verina-advanced-75-integer-listp (sequence)
  (declare (xargs :measure (acl2-count sequence)))
  (if (consp sequence)
      (and
       (integerp (car sequence))
       (verina-advanced-75-integer-listp
        (cdr sequence)))
    (equal sequence nil)))

(defun verina-advanced-75-task-code-precond (sequence)
  (< 0 (len sequence)))

(defun verina-advanced-75-task-code-fold
    (remaining current maximum-so-far)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((x (car remaining))
             (extended (+ current x))
             (new-current
              (if (>= extended x)
                  extended
                x))
             (new-maximum
              (if (>= maximum-so-far new-current)
                  maximum-so-far
                new-current)))
        (verina-advanced-75-task-code-fold
         (cdr remaining)
         new-current
         new-maximum))
    maximum-so-far))

;; The proof-valued precondition argument is computationally irrelevant in
;; Lean and is erased here. The empty branch, first-element initialization,
;; and every left-fold update are otherwise exactly the source implementation.

(defun verina-advanced-75-task-code (sequence)
  (if (consp sequence)
      (verina-advanced-75-task-code-fold
       (cdr sequence)
       (car sequence)
       (car sequence))
    0))

(defun verina-advanced-75-drop (count sequence)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      sequence
    (if (consp sequence)
        (verina-advanced-75-drop
         (- count 1)
         (cdr sequence))
      nil)))

(defun verina-advanced-75-take (count sequence)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp sequence)
        (cons
         (car sequence)
         (verina-advanced-75-take
          (- count 1)
          (cdr sequence)))
      nil)))

(defun verina-advanced-75-list-sum (sequence)
  (declare (xargs :measure (acl2-count sequence)))
  (if (consp sequence)
      (+
       (car sequence)
       (verina-advanced-75-list-sum
        (cdr sequence)))
    0))

;; For each source start index, the postcondition first constructs lengths
;; 0 through n-start and then filters out the unique empty length-zero slice.
;; The following recursion therefore produces exactly the surviving sums, in
;; the same order, for lengths 1 through n-start.

(defun verina-advanced-75-subarray-sums-at-start
    (sequence start length remaining-lengths)
  (declare (xargs :measure (nfix remaining-lengths)))
  (if (zp remaining-lengths)
      nil
    (cons
     (verina-advanced-75-list-sum
      (verina-advanced-75-take
       length
       (verina-advanced-75-drop
        start
        sequence)))
     (verina-advanced-75-subarray-sums-at-start
      sequence
      start
      (+ length 1)
      (- remaining-lengths 1)))))

;; START ranges from zero through n, as in List.range (n + 1). At start n the
;; source produces only an empty slice, which its filter removes; hence that
;; iteration contributes nil here. APPEND preserves flatMap traversal order.

(defun verina-advanced-75-all-subarray-sums-from
    (sequence start remaining-starts total-length)
  (declare (xargs :measure (nfix remaining-starts)))
  (if (zp remaining-starts)
      nil
    (append
     (verina-advanced-75-subarray-sums-at-start
      sequence
      start
      1
      (nfix (- total-length start)))
     (verina-advanced-75-all-subarray-sums-from
      sequence
      (+ start 1)
      (- remaining-starts 1)
      total-length))))

(defun verina-advanced-75-all-subarray-sums (sequence)
  (let ((total-length (len sequence)))
    (verina-advanced-75-all-subarray-sums-from
     sequence
     0
     (+ total-length 1)
     total-length)))

(defun verina-advanced-75-contains-result-p
    (subarray-sums result)
  (declare (xargs :measure (acl2-count subarray-sums)))
  (if (consp subarray-sums)
      (or
       (equal (car subarray-sums) result)
       (verina-advanced-75-contains-result-p
        (cdr subarray-sums)
        result))
    nil))

(defun verina-advanced-75-all-sums-at-most-result-p
    (subarray-sums result)
  (declare (xargs :measure (acl2-count subarray-sums)))
  (if (consp subarray-sums)
      (and
       (<= (car subarray-sums) result)
       (verina-advanced-75-all-sums-at-most-result-p
        (cdr subarray-sums)
        result))
    t))

(defun verina-advanced-75-task-code-postcond
    (sequence result)
  (let ((subarray-sums
         (verina-advanced-75-all-subarray-sums
          sequence)))
    (and
     (verina-advanced-75-integer-listp sequence)
     (integerp result)
     (verina-advanced-75-contains-result-p
      subarray-sums
      result)
     (verina-advanced-75-all-sums-at-most-result-p
      subarray-sums
      result))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and nonempty precondition; its
;; conclusion applies the complete postcondition to the exact executable
;; result.

(defun verina-advanced-75-task-code-spec-satisfied-statement
    (sequence)
  (implies
   (and
    (verina-advanced-75-integer-listp sequence)
    (verina-advanced-75-task-code-precond sequence))
   (verina-advanced-75-task-code-postcond
    sequence
    (verina-advanced-75-task-code sequence))))

(value-triple :itpeval-statement-checked)
:q
