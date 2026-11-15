;; Statement-only formalization of VERINA corpus artifact verina_advanced_53,
;; "minimumRightShifts": the executable search returns the minimum number of
;; cyclic right shifts that makes a distinct integer list nondecreasing, or
;; -1 when no such shift exists. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-53-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-53-integer-listp (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-53-no-duplicates-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (not (member-equal (car xs) (cdr xs)))
       (verina-advanced-53-no-duplicates-p (cdr xs)))
    (equal xs nil)))

;; The List Int binder supplies the element domain. The source precondition
;; itself is exactly List.Nodup.

(defun verina-advanced-53-minimum-right-shifts-precond (nums)
  (verina-advanced-53-no-duplicates-p nums))

;; This is the source executable helper isSortedAux: it checks adjacent
;; elements from left to right and stops at the first decreasing pair.

(defun verina-advanced-53-is-sorted-aux-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (consp (cdr xs))
          (if (<= (car xs) (car (cdr xs)))
              (verina-advanced-53-is-sorted-aux-p (cdr xs))
            nil)
        t)
    t))

;; Reversing exposes the original last element, which is moved to the front
;; while the remainder is restored to its original order.

(defun verina-advanced-53-right-shift-once (xs)
  (let ((rev (reverse xs)))
    (if (consp rev)
        (cons (car rev) (reverse (cdr rev)))
      nil)))

;; REMAINING is n - shifts-count. Thus zero implements the source guard
;; shifts_count >= n; otherwise CURRENT is checked and the exact next right
;; shift is explored.

(defun verina-advanced-53-check-shifts
    (remaining shifts-count current)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      -1
    (if (verina-advanced-53-is-sorted-aux-p current)
        shifts-count
      (verina-advanced-53-check-shifts
       (- remaining 1)
       (+ shifts-count 1)
       (verina-advanced-53-right-shift-once current)))))

;; The proof-valued precondition argument is computationally irrelevant in
;; Lean and is erased here. The branches and search order are otherwise the
;; source program verbatim.

(defun verina-advanced-53-minimum-right-shifts (nums)
  (let ((n (len nums)))
    (if (<= n 1)
        0
      (if (verina-advanced-53-is-sorted-aux-p nums)
          0
        (verina-advanced-53-check-shifts
         (- n 1)
         1
         (verina-advanced-53-right-shift-once nums))))))

;; Lean's List.Pairwise (fun x y => x <= y) requires each head to be at most
;; every later element, recursively.

(defun verina-advanced-53-head-at-most-all-p (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (<= x (car xs))
       (verina-advanced-53-head-at-most-all-p x (cdr xs)))
    t))

(defun verina-advanced-53-pairwise-nondecreasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (verina-advanced-53-head-at-most-all-p
        (car xs)
        (cdr xs))
       (verina-advanced-53-pairwise-nondecreasing-p (cdr xs)))
    t))

;; Repeating the exact one-step operation COUNT times is List.rotateRight
;; COUNT on the counts used by the source postcondition.

(defun verina-advanced-53-rotate-right (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      xs
    (verina-advanced-53-rotate-right
     (- count 1)
     (verina-advanced-53-right-shift-once xs))))

;; This downward recursion checks exactly List.range COUNT: all shift counts
;; from zero through COUNT - 1, with conjunction order reversed.

(defun verina-advanced-53-all-earlier-shifts-unsorted-p
    (count nums)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((k (- count 1)))
      (and
       (not
        (verina-advanced-53-pairwise-nondecreasing-p
         (verina-advanced-53-rotate-right k nums)))
       (verina-advanced-53-all-earlier-shifts-unsorted-p
        k
        nums)))))

(defun verina-advanced-53-minimum-right-shifts-postcond
    (nums result)
  (let ((n (len nums)))
    (and
     (verina-advanced-53-integer-listp nums)
     (integerp result)
     (if (<= n 1)
         (equal result 0)
       (or
        (and
         (<= 0 result)
         (< result n)
         (verina-advanced-53-pairwise-nondecreasing-p
          (verina-advanced-53-rotate-right
           (nfix result)
           nums))
         (verina-advanced-53-all-earlier-shifts-unsorted-p
          (nfix result)
          nums))
        (and
         (equal result -1)
         (verina-advanced-53-all-earlier-shifts-unsorted-p
          n
          nums)))))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and complete Nodup precondition;
;; its conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-53-minimum-right-shifts-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-53-integer-listp nums)
    (verina-advanced-53-minimum-right-shifts-precond nums))
   (verina-advanced-53-minimum-right-shifts-postcond
    nums
    (verina-advanced-53-minimum-right-shifts nums))))

(value-triple :itpeval-statement-checked)
:q
