;; Statement-only formalization of VERINA corpus artifact verina_advanced_80,
;; catalog title "twoSum": a fuel-bounded nested search on an integer array
;; returns two increasing in-bounds indices whose entries sum to the target,
;; under the unique-pair precondition. This file contains no proof.

(in-package "ACL2")

;; A Lean Array Int is represented exactly by its finite sequence of entries:
;; a proper ACL2 list whose elements are integers. Array Nat results are
;; represented analogously by proper lists of natural numbers.

(defun verina-advanced-80-integer-listp (values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (and
       (integerp (car values))
       (verina-advanced-80-integer-listp
        (cdr values)))
    (equal values nil)))

(defun verina-advanced-80-natural-listp (values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (and
       (natp (car values))
       (verina-advanced-80-natural-listp
        (cdr values)))
    (equal values nil)))

;; Array.get! returns the element at a natural index when it is in bounds and
;; the inhabited default zero otherwise. This definition serves both the
;; integer input array and the natural result array.

(defun verina-advanced-80-nth-default-zero
    (index values)
  (if (and
       (natp index)
       (< index (len values)))
      (nth index values)
    0))

;; These two recursions reproduce the nested List.any over
;; i in List.range nums.size and j in List.range i. Thus they inspect exactly
;; the pairs 0 <= j < i < nums.size from the source precondition.

(defun verina-advanced-80-has-matching-j-p
    (nums target i j remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (or
     (equal
      (+
       (verina-advanced-80-nth-default-zero i nums)
       (verina-advanced-80-nth-default-zero j nums))
      target)
     (verina-advanced-80-has-matching-j-p
      nums
      target
      i
      (+ j 1)
      (- remaining 1)))))

(defun verina-advanced-80-has-matching-pair-from-p
    (nums target i remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (or
     (verina-advanced-80-has-matching-j-p
      nums
      target
      i
      0
      i)
     (verina-advanced-80-has-matching-pair-from-p
      nums
      target
      (+ i 1)
      (- remaining 1)))))

;; These counting recursions reproduce the source range/flatMap/filter list,
;; including one occurrence per ordered lower-triangular index pair. Its
;; length is therefore exactly the number tested by the uniqueness conjunct.

(defun verina-advanced-80-count-matching-j
    (nums target i j remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
         (equal
          (+
           (verina-advanced-80-nth-default-zero i nums)
           (verina-advanced-80-nth-default-zero j nums))
          target)
         1
       0)
     (verina-advanced-80-count-matching-j
      nums
      target
      i
      (+ j 1)
      (- remaining 1)))))

(defun verina-advanced-80-count-matching-pairs-from
    (nums target i remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (verina-advanced-80-count-matching-j
      nums
      target
      i
      0
      i)
     (verina-advanced-80-count-matching-pairs-from
      nums
      target
      (+ i 1)
      (- remaining 1)))))

(defun verina-advanced-80-two-sum-precond
    (nums target)
  (and
   (<= 2 (len nums))
   (verina-advanced-80-has-matching-pair-from-p
    nums
    target
    0
    (len nums))
   (equal
    (verina-advanced-80-count-matching-pairs-from
     nums
     target
     0
     (len nums))
    1)))

;; This is the source-local findIndices recursion. The state is the same
;; (i, j, fuel) triple, fuel zero returns the empty array, and every recursive
;; branch passes the predecessor fuel. When j reaches the array size, the next
;; state is exactly (i + 1, i + 2).

(defun verina-advanced-80-find-indices
    (nums target i j fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      nil
    (if (>= i (len nums))
        nil
      (if (>= j (len nums))
          (verina-advanced-80-find-indices
           nums
           target
           (+ i 1)
           (+ i 2)
           (- fuel 1))
        (if
            (equal
             (+
              (verina-advanced-80-nth-default-zero i nums)
              (verina-advanced-80-nth-default-zero j nums))
             target)
            (list i j)
          (verina-advanced-80-find-indices
           nums
           target
           i
           (+ j 1)
           (- fuel 1)))))))

;; The proof-valued precondition argument is computationally irrelevant in
;; Lean and is erased here. The initial indices and fuel are unchanged.

(defun verina-advanced-80-two-sum (nums target)
  (verina-advanced-80-find-indices
   nums
   target
   0
   1
   (* (len nums) (len nums))))

;; This is the complete source postcondition: the natural array has length
;; two, both indices are in bounds and increasing, and the selected integer
;; entries sum to the target.

(defun verina-advanced-80-two-sum-postcond
    (nums target result)
  (and
   (verina-advanced-80-integer-listp nums)
   (integerp target)
   (verina-advanced-80-natural-listp result)
   (equal (len result) 2)
   (<
    (verina-advanced-80-nth-default-zero 0 result)
    (len nums))
   (<
    (verina-advanced-80-nth-default-zero 1 result)
    (len nums))
   (<
    (verina-advanced-80-nth-default-zero 0 result)
    (verina-advanced-80-nth-default-zero 1 result))
   (equal
    (+
     (verina-advanced-80-nth-default-zero
      (verina-advanced-80-nth-default-zero 0 result)
      nums)
     (verina-advanced-80-nth-default-zero
      (verina-advanced-80-nth-default-zero 1 result)
      nums))
    target)))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the Array Int and Int binder domains and the complete
;; source precondition; its conclusion applies the complete postcondition to
;; the exact executable result.

(defun
    verina-advanced-80-two-sum-spec-satisfied-statement
    (nums target)
  (implies
   (and
    (verina-advanced-80-integer-listp nums)
    (integerp target)
    (verina-advanced-80-two-sum-precond
     nums
     target))
   (verina-advanced-80-two-sum-postcond
    nums
    target
    (verina-advanced-80-two-sum
     nums
     target))))

(value-triple :itpeval-statement-checked)
:q
