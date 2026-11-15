;; Statement-only formalization of VERINA corpus artifact verina_advanced_30,
;; "longestIncreasingStreak": a deterministic recursive scan computes the
;; maximum length of a strictly increasing contiguous integer-list streak,
;; together with its exact maximal-streak contract. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-30-integer-listp (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (integerp (car nums))
       (verina-advanced-30-integer-listp (cdr nums)))
    (equal nums nil)))

;; The source precondition is True. The List Int binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-30-longest-increasing-streak-precond
    (nums)
  (declare (ignore nums))
  t)

(defun verina-advanced-30-nat-max (left right)
  (if (< left right)
      right
    left))

;; HAS-PREV distinguishes none from some PREV. Consuming one list cell per
;; call exactly reproduces the source local recursion and both state updates.

(defun verina-advanced-30-longest-increasing-streak-aux
    (lst has-prev prev curr-len max-len)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (let ((x (car lst))
            (xs (cdr lst)))
        (if has-prev
            (if (> x prev)
                (let ((next-curr-len (+ curr-len 1)))
                  (verina-advanced-30-longest-increasing-streak-aux
                   xs
                   t
                   x
                   next-curr-len
                   (verina-advanced-30-nat-max
                    next-curr-len
                    max-len)))
              (verina-advanced-30-longest-increasing-streak-aux
               xs
               t
               x
               1
               (verina-advanced-30-nat-max
                curr-len
                max-len)))
          (verina-advanced-30-longest-increasing-streak-aux
           xs
           t
           x
           1
           (verina-advanced-30-nat-max 1 max-len))))
    (verina-advanced-30-nat-max curr-len max-len)))

;; The proof-valued True precondition argument is computationally irrelevant.

(defun verina-advanced-30-longest-increasing-streak
    (nums)
  (verina-advanced-30-longest-increasing-streak-aux
   nums
   nil
   0
   0
   0))

;; List getElem! on Int returns the inhabited default 0 outside the list.

(defun verina-advanced-30-list-read (index nums)
  (if (and
       (natp index)
       (< index (len nums)))
      (nth index nums)
    0))

;; This is the postcondition's List.range (result - 1) followed by all:
;; every adjacent pair inside the candidate streak is strictly increasing.

(defun verina-advanced-30-streak-increasing-p
    (nums index remaining-pairs)
  (declare (xargs :measure (nfix remaining-pairs)))
  (if (zp remaining-pairs)
      t
    (and
     (<
      (verina-advanced-30-list-read index nums)
      (verina-advanced-30-list-read (+ index 1) nums))
     (verina-advanced-30-streak-increasing-p
      nums
      (+ index 1)
      (- remaining-pairs 1)))))

;; The four conjuncts reproduce the bounds, internal comparisons, and the two
;; non-extendability tests for one start index.

(defun verina-advanced-30-maximal-streak-at-p
    (nums start result)
  (and
   (<= (+ start result) (len nums))
   (verina-advanced-30-streak-increasing-p
    nums
    start
    (nfix (- result 1)))
   (or
    (equal start 0)
    (>=
     (verina-advanced-30-list-read
      (nfix (- start 1))
      nums)
     (verina-advanced-30-list-read start nums)))
   (or
    (equal (+ start result) (len nums))
    (>=
     (verina-advanced-30-list-read
      (nfix (- (+ start result) 1))
      nums)
     (verina-advanced-30-list-read
      (+ start result)
      nums)))))

;; Iterating START over exactly REMAINING-STARTS values implements List.any.

(defun verina-advanced-30-exists-maximal-streak-p
    (nums result start remaining-starts)
  (declare (xargs :measure (nfix remaining-starts)))
  (if (zp remaining-starts)
      nil
    (or
     (verina-advanced-30-maximal-streak-at-p
      nums
      start
      result)
     (verina-advanced-30-exists-maximal-streak-p
      nums
      result
      (+ start 1)
      (- remaining-starts 1)))))

;; For a proposed streak of length result + 1, this is List.range result.any:
;; either the next index is out of bounds or one adjacent comparison fails.

(defun verina-advanced-30-window-has-break-p
    (nums start offset remaining-pairs)
  (declare (xargs :measure (nfix remaining-pairs)))
  (if (zp remaining-pairs)
      nil
    (or
     (>= (+ start offset 1) (len nums))
     (>=
      (verina-advanced-30-list-read
       (+ start offset)
       nums)
      (verina-advanced-30-list-read
       (+ start offset 1)
       nums))
     (verina-advanced-30-window-has-break-p
      nums
      start
      (+ offset 1)
      (- remaining-pairs 1)))))

;; Iterating START over List.range (nums.length - result) implements the
;; postcondition's universal assertion that no longer streak exists.

(defun verina-advanced-30-no-longer-streak-p
    (nums result start remaining-starts)
  (declare (xargs :measure (nfix remaining-starts)))
  (if (zp remaining-starts)
      t
    (and
     (verina-advanced-30-window-has-break-p
      nums
      start
      0
      result)
     (verina-advanced-30-no-longer-streak-p
      nums
      result
      (+ start 1)
      (- remaining-starts 1)))))

(defun verina-advanced-30-longest-increasing-streak-postcond
    (nums result)
  (and
   (verina-advanced-30-integer-listp nums)
   (natp result)
   (implies
    (equal nums nil)
    (equal result 0))
   (implies
    (> result 0)
    (verina-advanced-30-exists-maximal-streak-p
     nums
     result
     0
     (+ (nfix (- (len nums) result)) 1)))
   (verina-advanced-30-no-longer-streak-p
    nums
    result
    0
    (nfix (- (len nums) result)))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and True precondition, and its
;; conclusion applies the full postcondition to the executable result.

(defun
    verina-advanced-30-longest-increasing-streak-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-30-integer-listp nums)
    (verina-advanced-30-longest-increasing-streak-precond nums))
   (verina-advanced-30-longest-increasing-streak-postcond
    nums
    (verina-advanced-30-longest-increasing-streak nums))))

(value-triple :itpeval-statement-checked)
:q
