;; Statement-only formalization of VERINA corpus artifact verina_advanced_62,
;; "rain": a deterministic two-pointer program computes trapped rainwater for
;; a nonnegative integer elevation list, with its result specified by the
;; corresponding prefix-and-suffix maximum sum. This file contains no proof.

(in-package "ACL2")

;; Lean's List Int domain is represented by proper ACL2 lists of integers.

(defun verina-advanced-62-integer-listp (heights)
  (declare (xargs :measure (acl2-count heights)))
  (if (consp heights)
      (and
       (integerp (car heights))
       (verina-advanced-62-integer-listp (cdr heights)))
    (equal heights nil)))

;; This is List.all (fun h => h >= 0) on the typed input list.

(defun verina-advanced-62-rain-precond (heights)
  (declare (xargs :measure (acl2-count heights)))
  (if (consp heights)
      (and
       (<= 0 (car heights))
       (verina-advanced-62-rain-precond (cdr heights)))
    (equal heights nil)))

;; Lean's List.get! on List Int returns zero when the index is out of bounds.

(defun verina-advanced-62-nth-default-zero (index values)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp values)
        (if (zp index)
            (car values)
          (verina-advanced-62-nth-default-zero
           (- index 1)
           (cdr values)))
      0)))

(defun verina-advanced-62-int-max (left right)
  (if (< left right)
      right
    left))

(defun verina-advanced-62-int-min (left right)
  (if (< left right)
      left
    right))

;; FUEL is initialized to RIGHT - LEFT and decreases with every pointer move.
;; On the typed top-level call it is therefore zero exactly when the source
;; recursion reaches LEFT >= RIGHT. The two branches otherwise preserve the
;; source pointer, maximum, and accumulated-water transitions exactly.

(defun verina-advanced-62-rain-aux
    (heights left right left-max right-max water fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or
       (zp fuel)
       (<= right left))
      water
    (let ((left-height
           (verina-advanced-62-nth-default-zero
            left
            heights))
          (right-height
           (verina-advanced-62-nth-default-zero
            right
            heights)))
      (if (<= left-height right-height)
          (let ((new-left-max
                 (verina-advanced-62-int-max
                  left-max
                  left-height))
                (new-water
                 (+
                  water
                  (verina-advanced-62-int-max
                   0
                   (- left-max left-height)))))
            (verina-advanced-62-rain-aux
             heights
             (+ left 1)
             right
             new-left-max
             right-max
             new-water
             (- fuel 1)))
        (let ((new-right-max
               (verina-advanced-62-int-max
                right-max
                right-height))
              (new-water
               (+
                water
                (verina-advanced-62-int-max
                 0
                 (- right-max right-height)))))
          (verina-advanced-62-rain-aux
           heights
           left
           (- right 1)
           left-max
           new-right-max
           new-water
           (- fuel 1)))))))

;; The proof-valued precondition argument is computationally irrelevant.
;; This preserves the short-list branch and the source initialization from
;; both endpoints.

(defun verina-advanced-62-rain (heights)
  (let ((n (len heights)))
    (if (< n 3)
        0
      (let ((right (- n 1)))
        (verina-advanced-62-rain-aux
         heights
         0
         right
         (verina-advanced-62-nth-default-zero 0 heights)
         (verina-advanced-62-nth-default-zero right heights)
         0
         right)))))

;; These recursions encode the postcondition's local ML and MR functions.
;; MAX-LEFT-AT includes indices 0 through I. MAX-RIGHT-AT includes indices I
;; through the final list position.

(defun verina-advanced-62-max-left-loop
    (heights index remaining max-so-far)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      max-so-far
    (verina-advanced-62-max-left-loop
     heights
     (+ index 1)
     (- remaining 1)
     (verina-advanced-62-int-max
      max-so-far
      (verina-advanced-62-nth-default-zero
       index
       heights)))))

(defun verina-advanced-62-max-left-at (heights index)
  (if (natp index)
      (verina-advanced-62-max-left-loop
       heights
       0
       (+ index 1)
       0)
    0))

(defun verina-advanced-62-max-right-loop
    (heights index remaining max-so-far)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      max-so-far
    (verina-advanced-62-max-right-loop
     heights
     (+ index 1)
     (- remaining 1)
     (verina-advanced-62-int-max
      max-so-far
      (verina-advanced-62-nth-default-zero
       index
       heights)))))

(defun verina-advanced-62-max-right-at (heights index)
  (if (natp index)
      (verina-advanced-62-max-right-loop
       heights
       index
       (nfix (- (len heights) index))
       0)
    0))

(defun verina-advanced-62-water-at (heights index)
  (verina-advanced-62-int-max
   0
   (-
    (verina-advanced-62-int-min
     (verina-advanced-62-max-left-at heights index)
     (verina-advanced-62-max-right-at heights index))
    (verina-advanced-62-nth-default-zero
     index
     heights))))

;; INDEX and REMAINING reproduce the postcondition's SUM-WATER recursion over
;; every index of the list in increasing order.

(defun verina-advanced-62-sum-water-loop
    (heights index remaining accumulator)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      accumulator
    (verina-advanced-62-sum-water-loop
     heights
     (+ index 1)
     (- remaining 1)
     (+
      accumulator
      (verina-advanced-62-water-at
       heights
       index)))))

(defun verina-advanced-62-sum-water (heights)
  (verina-advanced-62-sum-water-loop
   heights
   0
   (len heights)
   0))

(defun verina-advanced-62-rain-postcond
    (heights result)
  (and
   (verina-advanced-62-integer-listp heights)
   (integerp result)
   (<= 0 result)
   (if (< (len heights) 3)
       (equal result 0)
     (equal
      result
      (verina-advanced-62-sum-water heights)))))

;; This predicate is the unproved final correctness proposition connecting
;; the complete postcondition to the exact executable result.

(defun verina-advanced-62-rain-spec-satisfied-statement
    (heights)
  (implies
   (and
    (verina-advanced-62-integer-listp heights)
    (verina-advanced-62-rain-precond heights))
   (verina-advanced-62-rain-postcond
    heights
    (verina-advanced-62-rain heights))))

(value-triple :itpeval-statement-checked)
:q
