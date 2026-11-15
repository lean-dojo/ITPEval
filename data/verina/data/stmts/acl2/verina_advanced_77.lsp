;; Statement-only formalization of VERINA corpus artifact verina_advanced_77,
;; catalog title "trapRainWater": an exact two-pointer natural-list program
;; computes trapped rain water and satisfies its prefix/suffix-maximum
;; specification. This file contains no proof.

(in-package "ACL2")

;; Lean's List Nat domain is represented by proper ACL2 lists of naturals.

(defun verina-advanced-77-natural-listp (height)
  (declare (xargs :measure (acl2-count height)))
  (if (consp height)
      (and
       (natp (car height))
       (verina-advanced-77-natural-listp (cdr height)))
    (equal height nil)))

(defun verina-advanced-77-trap-rain-water-precond (height)
  (declare (ignore height))
  t)

;; This is Lean's truncated subtraction on naturals.

(defun verina-advanced-77-nat-sub (left right)
  (nfix (- (nfix left) (nfix right))))

;; List.get! returns the default natural zero outside the list.

(defun verina-advanced-77-nth-default-zero (index values)
  (if (and
       (natp index)
       (< index (len values)))
      (nfix (nth index values))
    0))

;; FUEL is exactly right - left. Every recursive source step either increments
;; LEFT or decrements RIGHT, so this is an exact operational presentation of
;; the source's well-founded recursion rather than an execution bound.

(defun verina-advanced-77-trap-loop-fuel
    (height left right left-max right-max water fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      water
    (if (< left right)
        (let ((height-left
               (verina-advanced-77-nth-default-zero
                left
                height))
              (height-right
               (verina-advanced-77-nth-default-zero
                right
                height)))
          (if (< height-left height-right)
              (if (>= height-left left-max)
                  (verina-advanced-77-trap-loop-fuel
                   height
                   (+ left 1)
                   right
                   height-left
                   right-max
                   water
                   (- fuel 1))
                (verina-advanced-77-trap-loop-fuel
                 height
                 (+ left 1)
                 right
                 left-max
                 right-max
                 (+ water
                    (verina-advanced-77-nat-sub
                     left-max
                     height-left))
                 (- fuel 1)))
            (if (>= height-right right-max)
                (verina-advanced-77-trap-loop-fuel
                 height
                 left
                 (verina-advanced-77-nat-sub right 1)
                 left-max
                 height-right
                 water
                 (- fuel 1))
              (verina-advanced-77-trap-loop-fuel
               height
               left
               (verina-advanced-77-nat-sub right 1)
               left-max
               right-max
               (+ water
                  (verina-advanced-77-nat-sub
                   right-max
                   height-right))
               (- fuel 1)))))
      water)))

(defun verina-advanced-77-trap-loop
    (height left right left-max right-max water)
  (verina-advanced-77-trap-loop-fuel
   height
   left
   right
   left-max
   right-max
   water
   (verina-advanced-77-nat-sub right left)))

;; The proof-valued precondition argument is computationally irrelevant in
;; Lean and is erased here. All remaining arguments and initial values are
;; exactly those of trapRainWater.

(defun verina-advanced-77-trap-rain-water (height)
  (verina-advanced-77-trap-loop
   height
   0
   (verina-advanced-77-nat-sub (len height) 1)
   0
   0
   0))

;; These helpers reproduce List.take, List.drop, and foldl Nat.max 0.

(defun verina-advanced-77-take (count values)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp values)
        (cons
         (car values)
         (verina-advanced-77-take
          (- count 1)
          (cdr values)))
      nil)))

(defun verina-advanced-77-drop (count values)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      values
    (if (consp values)
        (verina-advanced-77-drop
         (- count 1)
         (cdr values))
      nil)))

(defun verina-advanced-77-fold-max (values accumulator)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (verina-advanced-77-fold-max
       (cdr values)
       (if (>= (car values) accumulator)
           (car values)
         accumulator))
    accumulator))

(defun verina-advanced-77-nat-min (left right)
  (if (<= left right)
      left
    right))

;; This is the postcondition's waterAt value for one index.

(defun verina-advanced-77-water-at-index (height index)
  (let* ((left-max
          (verina-advanced-77-fold-max
           (verina-advanced-77-take
            (+ index 1)
            height)
           0))
         (right-max
          (verina-advanced-77-fold-max
           (verina-advanced-77-drop index height)
           0))
         (bounded-height
          (verina-advanced-77-nat-min
           left-max
           right-max)))
    (verina-advanced-77-nat-sub
     bounded-height
     (verina-advanced-77-nth-default-zero
      index
      height))))

;; These functions reproduce List.range height.length, its map by waterAt, and
;; the final left fold by natural addition.

(defun verina-advanced-77-range-from
    (index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     index
     (verina-advanced-77-range-from
      (+ index 1)
      (- remaining 1)))))

(defun verina-advanced-77-range (count)
  (verina-advanced-77-range-from 0 count))

(defun verina-advanced-77-map-water-at
    (indices height)
  (declare (xargs :measure (acl2-count indices)))
  (if (consp indices)
      (cons
       (verina-advanced-77-water-at-index
        height
        (car indices))
       (verina-advanced-77-map-water-at
        (cdr indices)
        height))
    nil))

(defun verina-advanced-77-fold-sum
    (values accumulator)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (verina-advanced-77-fold-sum
       (cdr values)
       (+ accumulator (car values)))
    accumulator))

(defun verina-advanced-77-expected-water (height)
  (verina-advanced-77-fold-sum
   (verina-advanced-77-map-water-at
    (verina-advanced-77-range (len height))
    height)
   0))

;; The two conjuncts deliberately preserve the source Nat subtraction
;; formulation rather than replacing it textually by equality.

(defun verina-advanced-77-trap-rain-water-postcond
    (height result)
  (let ((expected
         (verina-advanced-77-expected-water height)))
    (and
     (verina-advanced-77-natural-listp height)
     (natp result)
     (equal
      (verina-advanced-77-nat-sub result expected)
      0)
     (<= expected result))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Nat binder and source precondition; its
;; conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-77-trap-rain-water-spec-satisfied-statement
    (height)
  (implies
   (and
    (verina-advanced-77-natural-listp height)
    (verina-advanced-77-trap-rain-water-precond height))
   (verina-advanced-77-trap-rain-water-postcond
    height
    (verina-advanced-77-trap-rain-water height))))

(value-triple :itpeval-statement-checked)
:q
