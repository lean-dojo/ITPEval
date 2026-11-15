;; Statement-only formalization of VERINA corpus artifact verina_advanced_38,
;; "maxCoverageAfterRemovingOne": removing each interval in turn, stably
;; sorting the remainder by its left endpoint, merging overlaps, and summing
;; spans computes the maximum resulting coverage. This file contains no proof.

(in-package "ACL2")

;; A Lean Nat pair is represented canonically by an ACL2 cons pair, and a
;; List (Prod Nat Nat) by a proper ACL2 list of such pairs.

(defun verina-advanced-38-nat-interval-p (interval)
  (and
   (consp interval)
   (natp (car interval))
   (natp (cdr interval))))

(defun verina-advanced-38-nat-interval-listp (intervals)
  (declare (xargs :measure (acl2-count intervals)))
  (if (consp intervals)
      (and
       (verina-advanced-38-nat-interval-p
        (car intervals))
       (verina-advanced-38-nat-interval-listp
        (cdr intervals)))
    (equal intervals nil)))

(defun verina-advanced-38-max-coverage-precond (intervals)
  (< 0 (len intervals)))

;; This is List.eraseIdx. Under every use below the index is in range; the
;; total out-of-range behavior also agrees with eraseIdx.

(defun verina-advanced-38-erase-index (intervals index)
  (declare (xargs :measure (acl2-count intervals)))
  (if (consp intervals)
      (if (zp index)
          (cdr intervals)
        (cons
         (car intervals)
         (verina-advanced-38-erase-index
          (cdr intervals)
          (- index 1))))
    nil))

;; Lean's List.mergeSort is stable. For the total preorder comparing only
;; left endpoints, this stable insertion sort returns exactly the same list:
;; endpoints increase, and equal-endpoint intervals retain their input order.

(defun verina-advanced-38-stable-insert
    (interval sorted)
  (declare (xargs :measure (acl2-count sorted)))
  (if (consp sorted)
      (if (<= (car interval)
              (car (car sorted)))
          (cons interval sorted)
        (cons
         (car sorted)
         (verina-advanced-38-stable-insert
          interval
          (cdr sorted))))
    (list interval)))

(defun verina-advanced-38-stable-sort (intervals)
  (declare (xargs :measure (acl2-count intervals)))
  (if (consp intervals)
      (verina-advanced-38-stable-insert
       (car intervals)
       (verina-advanced-38-stable-sort
        (cdr intervals)))
    nil))

(defun verina-advanced-38-nat-max (left right)
  (if (< left right)
      right
    left))

;; This left fold is the source merged computation. The accumulator is kept
;; in reverse order: an overlap replaces its head with the enlarged interval,
;; while a gap pushes the current interval.

(defun verina-advanced-38-merge-fold
    (sorted accumulator)
  (declare (xargs :measure (acl2-count sorted)))
  (if (consp sorted)
      (let ((current (car sorted)))
        (if (consp accumulator)
            (let* ((previous (car accumulator))
                   (start (car previous))
                   (end (cdr previous)))
              (if (<= (car current) end)
                  (verina-advanced-38-merge-fold
                   (cdr sorted)
                   (cons
                    (cons
                     start
                     (verina-advanced-38-nat-max
                      end
                      (cdr current)))
                    (cdr accumulator)))
                (verina-advanced-38-merge-fold
                 (cdr sorted)
                 (cons current accumulator))))
          (verina-advanced-38-merge-fold
           (cdr sorted)
           (list current))))
    accumulator))

;; NFIX reproduces Nat subtraction, so an interval whose right endpoint is
;; below its left endpoint contributes zero exactly as in Lean.

(defun verina-advanced-38-coverage-fold
    (merged accumulator)
  (declare (xargs :measure (acl2-count merged)))
  (if (consp merged)
      (let ((interval (car merged)))
        (verina-advanced-38-coverage-fold
         (cdr merged)
         (+ accumulator
            (nfix
             (- (cdr interval)
                (car interval))))))
    accumulator))

(defun verina-advanced-38-coverage-after-removing
    (intervals index)
  (let* ((remaining
          (verina-advanced-38-erase-index
           intervals
           index))
         (sorted
          (verina-advanced-38-stable-sort
           remaining))
         (merged-reversed
          (verina-advanced-38-merge-fold
           sorted
           nil)))
    (verina-advanced-38-coverage-fold
     (reverse merged-reversed)
     0)))

;; INDEX and REMAINING reproduce List.range intervals.length and its foldl.

(defun verina-advanced-38-max-coverage-scan
    (intervals index remaining accumulator)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      accumulator
    (let ((coverage
           (verina-advanced-38-coverage-after-removing
            intervals
            index)))
      (verina-advanced-38-max-coverage-scan
       intervals
       (+ index 1)
       (- remaining 1)
       (verina-advanced-38-nat-max
        accumulator
        coverage)))))

;; The proof-valued precondition argument has no computational content.
;; This definition preserves the length branch and complete range fold.

(defun verina-advanced-38-max-coverage-after-removing-one
    (intervals)
  (let ((length (len intervals)))
    (if (<= length 1)
        0
      (verina-advanced-38-max-coverage-scan
       intervals
       0
       length
       0))))

;; These two finite recursions are exactly the bounded universal and
;; existential quantifiers in the postcondition; the maximizing index remains
;; internal to the postcondition.

(defun verina-advanced-38-all-coverages-at-most-p
    (intervals bound index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (<=
      (verina-advanced-38-coverage-after-removing
       intervals
       index)
      bound)
     (verina-advanced-38-all-coverages-at-most-p
      intervals
      bound
      (+ index 1)
      (- remaining 1)))))

(defun verina-advanced-38-maximizing-index-exists-p
    (intervals result index remaining total-length)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (let ((coverage
           (verina-advanced-38-coverage-after-removing
            intervals
            index)))
      (or
       (and
        (equal result coverage)
        (verina-advanced-38-all-coverages-at-most-p
         intervals
         coverage
         0
         total-length))
       (verina-advanced-38-maximizing-index-exists-p
        intervals
        result
        (+ index 1)
        (- remaining 1)
        total-length)))))

(defun verina-advanced-38-max-coverage-postcond
    (intervals result)
  (let ((length (len intervals)))
    (and
     (natp result)
     (verina-advanced-38-maximizing-index-exists-p
      intervals
      result
      0
      length
      length))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List (Prod Nat Nat) binder and nonempty-list
;; precondition; its conclusion applies the complete postcondition to the
;; deterministic executable result.

(defun
    verina-advanced-38-max-coverage-after-removing-one-spec-satisfied-statement
    (intervals)
  (implies
   (and
    (verina-advanced-38-nat-interval-listp
     intervals)
    (verina-advanced-38-max-coverage-precond
     intervals))
   (verina-advanced-38-max-coverage-postcond
    intervals
    (verina-advanced-38-max-coverage-after-removing-one
     intervals))))

(value-triple :itpeval-statement-checked)
:q
