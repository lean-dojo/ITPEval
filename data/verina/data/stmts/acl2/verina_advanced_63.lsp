;; Statement-only formalization of VERINA corpus artifact verina_advanced_63,
;; "removeDuplicates": on a nondecreasing integer list, the deterministic
;; adjacent-change counter returns the length of the list with duplicates
;; erased. This file contains no proof.

(in-package "ACL2")

;; Lean's List Int domain is represented by proper ACL2 lists of integers.

(defun verina-advanced-63-integer-listp (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (integerp (car nums))
       (verina-advanced-63-integer-listp (cdr nums)))
    (equal nums nil)))

;; List.Pairwise (fun x y => x <= y) requires every head to be at most every
;; later element, recursively.

(defun verina-advanced-63-head-at-most-all-p (head tail)
  (declare (xargs :measure (acl2-count tail)))
  (if (consp tail)
      (and
       (<= head (car tail))
       (verina-advanced-63-head-at-most-all-p
        head
        (cdr tail)))
    (equal tail nil)))

(defun verina-advanced-63-pairwise-nondecreasing-p (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (verina-advanced-63-head-at-most-all-p
        (car nums)
        (cdr nums))
       (verina-advanced-63-pairwise-nondecreasing-p
        (cdr nums)))
    (equal nums nil)))

(defun verina-advanced-63-remove-duplicates-precond (nums)
  (verina-advanced-63-pairwise-nondecreasing-p nums))

;; This is the source-local countUniques recursion. PREV is the last distinct
;; integer seen, XS is the unprocessed suffix, and K is the current count.

(defun verina-advanced-63-count-uniques (prev xs k)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal (car xs) prev)
          (verina-advanced-63-count-uniques
           prev
           (cdr xs)
           k)
        (verina-advanced-63-count-uniques
         (car xs)
         (cdr xs)
         (+ k 1)))
    k))

;; The proof-valued precondition argument is computationally irrelevant.
;; The empty branch and the nonempty initialization at count one are exactly
;; those of the Lean implementation.

(defun verina-advanced-63-remove-duplicates (nums)
  (if (consp nums)
      (verina-advanced-63-count-uniques
       (car nums)
       (cdr nums)
       1)
    0))

;; Lean's List.eraseDups scans left to right, keeps the first occurrence of
;; each integer, accumulates those occurrences in reverse order, and reverses
;; the accumulator when the input is exhausted.

(defun verina-advanced-63-erase-dups-loop
    (remaining seen-reversed)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (member-equal (car remaining) seen-reversed)
          (verina-advanced-63-erase-dups-loop
           (cdr remaining)
           seen-reversed)
        (verina-advanced-63-erase-dups-loop
         (cdr remaining)
         (cons (car remaining) seen-reversed)))
    (reverse seen-reversed)))

(defun verina-advanced-63-erase-dups (nums)
  (verina-advanced-63-erase-dups-loop nums nil))

;; NFIX of an integer difference is Lean's truncated Nat subtraction on
;; natural-number operands.

(defun verina-advanced-63-nat-sub (left right)
  (if (and (natp left) (natp right))
      (nfix (- left right))
    0))

(defun verina-advanced-63-remove-duplicates-postcond
    (nums result)
  (let ((unique-count
         (len (verina-advanced-63-erase-dups nums))))
    (and
     (verina-advanced-63-integer-listp nums)
     (natp result)
     (equal
      (verina-advanced-63-nat-sub
       result
       unique-count)
      0)
     (<= unique-count result))))

;; This predicate is the unproved final correctness proposition connecting
;; the complete postcondition to the exact executable result.

(defun
    verina-advanced-63-remove-duplicates-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-63-integer-listp nums)
    (verina-advanced-63-remove-duplicates-precond nums))
   (verina-advanced-63-remove-duplicates-postcond
    nums
    (verina-advanced-63-remove-duplicates nums))))

(value-triple :itpeval-statement-checked)
:q
