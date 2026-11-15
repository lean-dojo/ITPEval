;; Statement-only formalization of VERINA corpus artifact verina_advanced_47,
;; "mergeIntervals": a deterministic stable insertion sort and merge computes
;; integer intervals whose complete coverage, separation, endpoint, and
;; no-spurious-merge contract is stated below. This file contains no proof.

(in-package "ACL2")

;; A Lean Prod Int Int is represented canonically by an ACL2 cons pair, and a
;; List (Prod Int Int) by a proper ACL2 list of such pairs.

(defun verina-advanced-47-int-interval-p (interval)
  (and
   (consp interval)
   (integerp (car interval))
   (integerp (cdr interval))))

(defun verina-advanced-47-int-interval-listp (intervals)
  (declare (xargs :measure (acl2-count intervals)))
  (if (consp intervals)
      (and
       (verina-advanced-47-int-interval-p
        (car intervals))
       (verina-advanced-47-int-interval-listp
        (cdr intervals)))
    (equal intervals nil)))

;; This is List.all (fun (start, end) => start <= end).

(defun verina-advanced-47-merge-intervals-precond
    (intervals)
  (declare (xargs :measure (acl2-count intervals)))
  (if (consp intervals)
      (and
       (<= (car (car intervals))
           (cdr (car intervals)))
       (verina-advanced-47-merge-intervals-precond
        (cdr intervals)))
    (equal intervals nil)))

;; These two functions are the source local insertion sort. Sorting the tail
;; before inserting the head and inserting before an equal start preserves the
;; source order among intervals with equal starts.

(defun verina-advanced-47-insert-interval
    (interval sorted)
  (declare (xargs :measure (acl2-count sorted)))
  (if (consp sorted)
      (if (<= (car interval)
              (car (car sorted)))
          (cons interval sorted)
        (cons
         (car sorted)
         (verina-advanced-47-insert-interval
          interval
          (cdr sorted))))
    (list interval)))

(defun verina-advanced-47-sort-intervals (intervals)
  (declare (xargs :measure (acl2-count intervals)))
  (if (consp intervals)
      (verina-advanced-47-insert-interval
       (car intervals)
       (verina-advanced-47-sort-intervals
        (cdr intervals)))
    nil))

(defun verina-advanced-47-int-max (left right)
  (if (< left right)
      right
    left))

;; The accumulator is the reversed output prefix. An overlapping interval
;; replaces its head with the same start and the larger end; a gap pushes the
;; current interval. The empty-input branch reverses the accumulator exactly
;; as in the source.

(defun verina-advanced-47-merge-sorted
    (sorted accumulator)
  (declare (xargs :measure (acl2-count sorted)))
  (if (consp sorted)
      (let ((current (car sorted)))
        (if (consp accumulator)
            (let ((previous (car accumulator)))
              (if (<= (car current)
                      (cdr previous))
                  (verina-advanced-47-merge-sorted
                   (cdr sorted)
                   (cons
                    (cons
                     (car previous)
                     (verina-advanced-47-int-max
                      (cdr previous)
                      (cdr current)))
                    (cdr accumulator)))
                (verina-advanced-47-merge-sorted
                 (cdr sorted)
                 (cons current accumulator))))
          (verina-advanced-47-merge-sorted
           (cdr sorted)
           (list current))))
    (reverse accumulator)))

;; The proof-valued precondition argument has no computational content. This
;; definition is the exact composition of the source sort and merge helpers.

(defun verina-advanced-47-merge-intervals (intervals)
  (verina-advanced-47-merge-sorted
   (verina-advanced-47-sort-intervals intervals)
   nil))

;; List.any for an output interval covering a fixed input interval.

(defun verina-advanced-47-covered-by-result-p
    (result start end)
  (declare (xargs :measure (acl2-count result)))
  (if (consp result)
      (or
       (and
        (<= (car (car result)) start)
        (<= end (cdr (car result))))
       (verina-advanced-47-covered-by-result-p
        (cdr result)
        start
        end))
    nil))

;; List.all over the input intervals for the source covered predicate.

(defun verina-advanced-47-all-inputs-covered-p
    (intervals result)
  (declare (xargs :measure (acl2-count intervals)))
  (if (consp intervals)
      (and
       (verina-advanced-47-covered-by-result-p
        result
        (car (car intervals))
        (cdr (car intervals)))
       (verina-advanced-47-all-inputs-covered-p
        (cdr intervals)
        result))
    (equal intervals nil)))

;; This is the source noOverlap recursion: lists of length zero or one pass,
;; and every adjacent pair must satisfy previous.end < next.start.

(defun verina-advanced-47-no-overlap-p (result)
  (declare (xargs :measure (acl2-count result)))
  (if (and (consp result)
           (consp (cdr result)))
      (and
       (< (cdr (car result))
          (car (car (cdr result))))
       (verina-advanced-47-no-overlap-p
        (cdr result)))
    t))

(defun verina-advanced-47-has-start-p
    (intervals start)
  (declare (xargs :measure (acl2-count intervals)))
  (if (consp intervals)
      (or
       (equal (car (car intervals)) start)
       (verina-advanced-47-has-start-p
        (cdr intervals)
        start))
    nil))

(defun verina-advanced-47-has-end-p
    (intervals end)
  (declare (xargs :measure (acl2-count intervals)))
  (if (consp intervals)
      (or
       (equal (cdr (car intervals)) end)
       (verina-advanced-47-has-end-p
        (cdr intervals)
        end))
    nil))

;; List.all for resultBounded: each result start and end separately occurs as
;; an input start and an input end.

(defun verina-advanced-47-result-bounded-p
    (result intervals)
  (declare (xargs :measure (acl2-count result)))
  (if (consp result)
      (and
       (verina-advanced-47-has-start-p
        intervals
        (car (car result)))
       (verina-advanced-47-has-end-p
        intervals
        (cdr (car result)))
       (verina-advanced-47-result-bounded-p
        (cdr result)
        intervals))
    (equal result nil)))

;; This List.any is the internal witness in noSpuriousMerge. The witness is an
;; input interval contained in the same result interval, starting earlier than
;; START and ending at or after START.

(defun verina-advanced-47-has-overlapping-predecessor-p
    (intervals result-start result-end start)
  (declare (xargs :measure (acl2-count intervals)))
  (if (consp intervals)
      (let ((candidate (car intervals)))
        (or
         (and
          (<= result-start (car candidate))
          (<= (cdr candidate) result-end)
          (< (car candidate) start)
          (>= (cdr candidate) start))
         (verina-advanced-47-has-overlapping-predecessor-p
          (cdr intervals)
          result-start
          result-end
          start)))
    nil))

;; This recursion is List.filter by containment followed by List.all. Inputs
;; outside the result interval are skipped; every contained input either starts
;; at the result start or has the source's overlapping-predecessor witness.

(defun verina-advanced-47-contained-inputs-connected-p
    (remaining all-intervals result-start result-end)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((current (car remaining))
             (start (car current))
             (end (cdr current))
             (contained
              (and
               (<= result-start start)
               (<= end result-end))))
        (and
         (if contained
             (or
              (equal start result-start)
              (verina-advanced-47-has-overlapping-predecessor-p
               all-intervals
               result-start
               result-end
               start))
           t)
         (verina-advanced-47-contained-inputs-connected-p
          (cdr remaining)
          all-intervals
          result-start
          result-end)))
    (equal remaining nil)))

;; List.all over the result intervals for noSpuriousMerge.

(defun verina-advanced-47-no-spurious-merge-p
    (result intervals)
  (declare (xargs :measure (acl2-count result)))
  (if (consp result)
      (let ((current (car result)))
        (and
         (verina-advanced-47-contained-inputs-connected-p
          intervals
          intervals
          (car current)
          (cdr current))
         (verina-advanced-47-no-spurious-merge-p
          (cdr result)
          intervals)))
    (equal result nil)))

(defun verina-advanced-47-merge-intervals-postcond
    (intervals result)
  (and
   (verina-advanced-47-int-interval-listp intervals)
   (verina-advanced-47-int-interval-listp result)
   (verina-advanced-47-all-inputs-covered-p
    intervals
    result)
   (verina-advanced-47-no-overlap-p result)
   (verina-advanced-47-result-bounded-p
    result
    intervals)
   (verina-advanced-47-no-spurious-merge-p
    result
    intervals)))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List (Prod Int Int) binder and complete source
;; precondition; its conclusion applies the complete postcondition to the
;; exact deterministic executable result.

(defun
    verina-advanced-47-merge-intervals-spec-satisfied-statement
    (intervals)
  (implies
   (and
    (verina-advanced-47-int-interval-listp intervals)
    (verina-advanced-47-merge-intervals-precond
     intervals))
   (verina-advanced-47-merge-intervals-postcond
    intervals
    (verina-advanced-47-merge-intervals intervals))))

(value-triple :itpeval-statement-checked)
:q
