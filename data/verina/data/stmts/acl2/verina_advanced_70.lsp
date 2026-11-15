;; Statement-only formalization of VERINA corpus artifact verina_advanced_70,
;; "semiOrderedPermutation": for a permutation of the integers from 1 through
;; its positive length, an exact index-based computation gives the minimum
;; adjacent swaps needed to place 1 first and the length last. This file
;; contains no proof.

(in-package "ACL2")

;; Lean's List Int domain is represented by proper ACL2 lists of integers.

(defun verina-advanced-70-integer-listp (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (integerp (car nums))
       (verina-advanced-70-integer-listp (cdr nums)))
    (equal nums nil)))

;; This recursion is List.Nodup.

(defun verina-advanced-70-no-duplicates-p (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (not (member-equal (car nums) (cdr nums)))
       (verina-advanced-70-no-duplicates-p (cdr nums)))
    (equal nums nil)))

;; This is List.all (fun x => 1 <= x and x <= Int.ofNat n).

(defun verina-advanced-70-all-in-range-p (nums n)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (<= 1 (car nums))
       (<= (car nums) n)
       (verina-advanced-70-all-in-range-p (cdr nums) n))
    (equal nums nil)))

(defun verina-advanced-70-semi-ordered-permutation-precond
    (nums)
  (let ((n (len nums)))
    (and
     (< 0 n)
     (verina-advanced-70-no-duplicates-p nums)
     (verina-advanced-70-all-in-range-p nums n))))

;; This is List.idxOf. Failure at the empty suffix returns zero, so an absent
;; value in a nonempty list returns the list length through the increments.

(defun verina-advanced-70-index-of (value nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (if (equal (car nums) value)
          0
        (+ 1
           (verina-advanced-70-index-of value (cdr nums))))
    0))

;; NFIX of an integer difference is Lean's truncated Nat subtraction.

(defun verina-advanced-70-nat-sub (left right)
  (if (and (natp left) (natp right))
      (nfix (- left right))
    0))

;; The proof-valued precondition argument is computationally irrelevant in
;; Lean and is erased here. Every let-bound index, distance, conditional, and
;; truncated subtraction below follows the source executable definition.

(defun verina-advanced-70-semi-ordered-permutation (nums)
  (let* ((length-list (len nums))
         (num-one 1)
         (largest-num length-list)
         (first-index
          (verina-advanced-70-index-of num-one nums))
         (last-index
          (verina-advanced-70-index-of largest-num nums))
         (start-position 0)
         (end-position
          (verina-advanced-70-nat-sub length-list 1))
         (should-move-one
          (not (equal first-index start-position)))
         (should-move-last
          (not (equal last-index end-position)))
         (distance-one
          (if should-move-one first-index 0))
         (distance-last
          (if should-move-last
              (verina-advanced-70-nat-sub
               end-position
               last-index)
            0))
         (total-moves (+ distance-one distance-last))
         (need-adjustment (> first-index last-index))
         (adjusted-moves
          (if need-adjustment
              (verina-advanced-70-nat-sub total-moves 1)
            total-moves)))
    adjusted-moves))

(defun verina-advanced-70-semi-ordered-permutation-postcond
    (nums result)
  (let* ((n (len nums))
         (pos1 (verina-advanced-70-index-of 1 nums))
         (posn (verina-advanced-70-index-of n nums)))
    (and
     (verina-advanced-70-integer-listp nums)
     (integerp result)
     (if (> pos1 posn)
         (equal
          (+ pos1 n)
          (+ result 2 posn))
       (equal
        (+ pos1 n)
        (+ result 1 posn))))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and complete source precondition;
;; its conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-70-semi-ordered-permutation-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-70-integer-listp nums)
    (verina-advanced-70-semi-ordered-permutation-precond nums))
   (verina-advanced-70-semi-ordered-permutation-postcond
    nums
    (verina-advanced-70-semi-ordered-permutation nums))))

(value-triple :itpeval-statement-checked)
:q
