;; Statement-only formalization of VERINA corpus artifact verina_advanced_54,
;; "missingNumber": the deterministic triangular-sum program returns the
;; unique natural number from zero through the input length that is absent
;; from a duplicate-free bounded list. This file contains no proof.

(in-package "ACL2")

;; Lean's List Nat domain is represented by proper ACL2 lists of naturals.

(defun verina-advanced-54-nat-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (natp (car xs))
       (verina-advanced-54-nat-listp (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-54-elements-at-most-p (xs upper-bound)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (<= (car xs) upper-bound)
       (verina-advanced-54-elements-at-most-p
        (cdr xs)
        upper-bound))
    (equal xs nil)))

(defun verina-advanced-54-no-duplicates-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (not (member-equal (car xs) (cdr xs)))
       (verina-advanced-54-no-duplicates-p (cdr xs)))
    (equal xs nil)))

;; This is exactly nums.all (fun x => x <= nums.length) together with
;; List.Nodup nums. The List Nat binder domain is explicit in the final
;; correctness proposition.

(defun verina-advanced-54-missing-number-precond (nums)
  (and
   (verina-advanced-54-elements-at-most-p nums (len nums))
   (verina-advanced-54-no-duplicates-p nums)))

;; This accumulator recursion is the source List.foldl addition with initial
;; value zero.

(defun verina-advanced-54-sum-foldl (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-54-sum-foldl
       (cdr remaining)
       (+ accumulator (car remaining)))
    accumulator))

;; FLOOR by two is Nat division on the nonnegative triangular product, and
;; NFIX of the difference is Lean's truncated Nat subtraction. The
;; proof-valued precondition argument is computationally erased.

(defun verina-advanced-54-missing-number (nums)
  (let* ((n (len nums))
         (expected-sum (floor (* n (+ n 1)) 2))
         (actual-sum
          (verina-advanced-54-sum-foldl nums 0)))
    (nfix (- expected-sum actual-sum))))

;; With COUNT = n + 1, this checks every natural x in List.range (n + 1).
;; The disjunction is equivalent to x != result -> x being a member of nums.

(defun verina-advanced-54-all-other-numbers-present-p
    (count result nums)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((x (- count 1)))
      (and
       (or
        (equal x result)
        (member-equal x nums))
       (verina-advanced-54-all-other-numbers-present-p
        x
        result
        nums)))))

(defun verina-advanced-54-missing-number-postcond
    (nums result)
  (let ((n (len nums)))
    (and
     (verina-advanced-54-nat-listp nums)
     (natp result)
     (< result (+ n 1))
     (not (member-equal result nums))
     (verina-advanced-54-all-other-numbers-present-p
      (+ n 1)
      result
      nums))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Nat binder and complete source precondition;
;; its conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-54-missing-number-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-54-nat-listp nums)
    (verina-advanced-54-missing-number-precond nums))
   (verina-advanced-54-missing-number-postcond
    nums
    (verina-advanced-54-missing-number nums))))

(value-triple :itpeval-statement-checked)
:q
