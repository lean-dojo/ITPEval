;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2017_odd_even_transposition_sort_Challenge3_odd_even_transposition_sortqtvc:
;; the odd-even transposition-sort verification condition, including
;; permutation, alternating sortedness, swaps, and inversion variants.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite ACL2 lists of mathematical integers represent the source
;; integer arrays without bounding either their lengths or their entries.

(defun oets-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (oets-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat sends negative integers to zero. Source list lookup is total,
;; with the inhabited integer default zero outside the list.

(defun oets-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun oets-nth-int (xs index)
  (let ((natural-index
         (oets-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; Source List.set changes an in-range natural index and otherwise leaves the
;; finite list unchanged.

(defun oets-list-set (xs index value)
  (declare (xargs :measure (nfix index)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (oets-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; This is the exact forward array swap from OLD to NEW. Both replacement
;; values are read from OLD.

(defun oets-array-exchange-p
    (old new first second)
  (equal
   new
   (oets-list-set
    (oets-list-set
     old
     (oets-int-to-nat first)
     (oets-nth-int old second))
    (oets-int-to-nat second)
    (oets-nth-int old first))))

;; Recursive deletion gives exact finite multiset equality, including
;; multiplicities, and hence the source array permutation predicate.

(defun oets-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (oets-permutation-p
      (cdr left)
      (remove1-equal (car left) right)))))

;; The recursive sum counts exactly the pairs i < j with a[j] < a[i], which
;; is the source definition of the inversion measure.

(defun oets-count-below (pivot xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      0
    (+
     (if (< (car xs) pivot) 1 0)
     (oets-count-below pivot (cdr xs)))))

(defun oets-inversions (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      0
    (+
     (oets-count-below (car xs) (cdr xs))
     (oets-inversions (cdr xs)))))

;; These predicates preserve the source universal quantifiers over
;; mathematical integer indices.

(defun-sk oets-sorted-p (xs)
  (forall (first second)
    (implies
     (and
      (integerp first)
      (integerp second))
     (implies
      (and
       (<= 0 first)
       (<= first second)
       (< second (len xs)))
      (<=
       (oets-nth-int xs first)
       (oets-nth-int xs second))))))

(defun-sk oets-odd-sorted-p (xs upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< (+ (* 2 index) 2) upper))
      (<=
       (oets-nth-int xs (+ (* 2 index) 1))
       (oets-nth-int xs (+ (* 2 index) 2)))))))

(defun-sk oets-even-sorted-p (xs upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< (+ (* 2 index) 1) upper))
      (<=
       (oets-nth-int xs (* 2 index))
       (oets-nth-int xs (+ (* 2 index) 1)))))))

;; Consequences of an odd-pass swap or no-swap step.

(defun oets-odd-swap-conclusion-p
    (original pass-start before after half-index index)
  (and
   (and
    (<= 0 (- (len before) index))
    (< (- (len after) (+ index 2))
       (- (len before) index)))
   (and
    (<= 0 (+ half-index 1))
    (<= 0 (+ index 2))
    (equal
     (+ index 2)
     (+ (* 2 (+ half-index 1)) 1)))
   (oets-permutation-p original after)
   (oets-odd-sorted-p after (+ index 2))
   (if (equal nil t)
       (equal
        (oets-inversions after)
        (oets-inversions pass-start))
     (<
      (oets-inversions after)
      (oets-inversions pass-start)))))

(defun-sk oets-all-odd-swap-results-p
    (original pass-start before half-index index swap-index)
  (forall (after)
    (implies
     (oets-integer-list-p after)
     (implies
      (equal (len after) (len before))
      (implies
       (oets-array-exchange-p
        before after index swap-index)
       (oets-odd-swap-conclusion-p
        original pass-start before after
        half-index index))))))

(defun oets-odd-no-swap-conclusion-p
    (original pass-start current half-index index odd-ok)
  (and
   (and
    (<= 0 (- (len current) index))
    (< (- (len current) (+ index 2))
       (- (len current) index)))
   (and
    (<= 0 (+ half-index 1))
    (<= 0 (+ index 2))
    (equal
     (+ index 2)
     (+ (* 2 (+ half-index 1)) 1)))
   (oets-permutation-p original current)
   (oets-odd-sorted-p current (+ index 2))
   (if (equal odd-ok t)
       (equal
        (oets-inversions current)
        (oets-inversions pass-start))
     (<
      (oets-inversions current)
      (oets-inversions pass-start)))))

;; Consequences of an even-pass swap or no-swap step.

(defun oets-even-swap-conclusion-p
    (original pass-start before after half-index index)
  (and
   (and
    (<= 0 (- (len before) index))
    (< (- (len after) (+ index 2))
       (- (len before) index)))
   (and
    (<= 0 (+ half-index 1))
    (<= 0 (+ index 2))
    (equal
     (+ index 2)
     (* 2 (+ half-index 1))))
   (<= 0 (+ index 2))
   (oets-permutation-p original after)
   (implies
    (equal nil t)
    (oets-odd-sorted-p after (len after)))
   (oets-even-sorted-p after (+ index 2))
   (if (equal nil t)
       (equal
        (oets-inversions after)
        (oets-inversions pass-start))
     (<
      (oets-inversions after)
      (oets-inversions pass-start)))
   (or
    (equal nil t)
    (<
     (oets-inversions after)
     (oets-inversions pass-start)))))

(defun-sk oets-all-even-swap-results-p
    (original pass-start before half-index index swap-index)
  (forall (after)
    (implies
     (oets-integer-list-p after)
     (implies
      (equal (len after) (len before))
      (implies
       (oets-array-exchange-p
        before after index swap-index)
       (oets-even-swap-conclusion-p
        original pass-start before after
        half-index index))))))

(defun oets-even-no-swap-conclusion-p
    (original pass-start current half-index index even-ok)
  (and
   (and
    (<= 0 (- (len current) index))
    (< (- (len current) (+ index 2))
       (- (len current) index)))
   (and
    (<= 0 (+ half-index 1))
    (<= 0 (+ index 2))
    (equal
     (+ index 2)
     (* 2 (+ half-index 1))))
   (<= 0 (+ index 2))
   (oets-permutation-p original current)
   (implies
    (equal even-ok t)
    (oets-odd-sorted-p current (len current)))
   (oets-even-sorted-p current (+ index 2))
   (if (equal even-ok t)
       (equal
        (oets-inversions current)
        (oets-inversions pass-start))
     (<
      (oets-inversions current)
      (oets-inversions pass-start)))
   (or
    (equal even-ok t)
    (<
     (oets-inversions current)
     (oets-inversions pass-start)))))

;; At the end of the even pass, preserve the complete lexicographic variant
;; decrease and outer-loop postcondition.

(defun oets-outer-loop-step-result-p
    (original outer-start current outer-ok current-ok)
  (let ((old-flag
         (if (equal outer-ok t) 0 1))
        (new-flag
         (if (equal current-ok t) 0 1)))
    (and
     (or
      (and
       (<= 0 old-flag)
       (< new-flag old-flag))
      (and
       (equal old-flag new-flag)
       (<= 0 (oets-inversions outer-start))
       (<
        (oets-inversions current)
        (oets-inversions outer-start))))
     (oets-permutation-p original current)
     (implies
      (equal current-ok t)
      (oets-sorted-p current)))))

;; One universally quantified state of the even-index pass.

(defun oets-even-loop-state-p
    (original pass-start current half-index even-ok)
  (let ((index (* 2 half-index)))
    (and
     (and
      (<= 0 half-index)
      (<= 0 index))
     (<= 0 index)
     (oets-permutation-p original current)
     (implies
      (equal even-ok t)
      (oets-odd-sorted-p current (len current)))
     (oets-even-sorted-p current index)
     (if (equal even-ok t)
         (equal
          (oets-inversions current)
          (oets-inversions pass-start))
       (<
        (oets-inversions current)
        (oets-inversions pass-start)))
     (or
      (equal even-ok t)
      (<
       (oets-inversions current)
       (oets-inversions pass-start))))))

(defun oets-even-loop-step-p
    (original pass-start current
              outer-ok half-index even-ok)
  (let ((index (* 2 half-index)))
    (if (< index (- (len current) 1))
        (let ((next-index (+ index 1)))
          (and
           (and
            (<= 0 next-index)
            (< next-index (len current)))
           (and
            (<= 0 index)
            (< index (len current)))
           (if (<
                (oets-nth-int current next-index)
                (oets-nth-int current index))
               (let ((swap-index (+ index 1)))
                 (and
                  (and
                   (and
                    (<= 0 index)
                    (< index (len current)))
                   (<= 0 swap-index)
                   (< swap-index (len current)))
                  (oets-all-even-swap-results-p
                   original pass-start current
                   half-index index swap-index)))
             (oets-even-no-swap-conclusion-p
              original pass-start current
              half-index index even-ok))))
      (oets-outer-loop-step-result-p
       original pass-start current
       outer-ok even-ok))))

(defun-sk oets-all-even-loop-states-p
    (original pass-start length-reference outer-ok)
  (forall (half-index even-ok current)
    (implies
     (and
      (integerp half-index)
      (booleanp even-ok)
      (oets-integer-list-p current))
     (implies
      (equal
       (len current)
       (len length-reference))
      (implies
       (oets-even-loop-state-p
        original pass-start current
        half-index even-ok)
       (oets-even-loop-step-p
        original pass-start current
        outer-ok half-index even-ok))))))

;; Exiting the odd pass establishes the exact initial even-loop invariant and
;; retains the universal continuation for the even pass.

(defun oets-odd-loop-exit-p
    (original pass-start current odd-ok outer-ok)
  (and
   (and
    (and
     (<= 0 0)
     (<= 0 0)
     (equal 0 (* 2 0)))
    (<= 0 0)
    (oets-permutation-p original current)
    (implies
     (equal odd-ok t)
     (oets-odd-sorted-p current (len current)))
    (oets-even-sorted-p current 0)
    (if (equal odd-ok t)
        (equal
         (oets-inversions current)
         (oets-inversions pass-start))
      (<
       (oets-inversions current)
       (oets-inversions pass-start)))
    (or
     (equal odd-ok t)
     (<
      (oets-inversions current)
      (oets-inversions pass-start))))
   (oets-all-even-loop-states-p
    original pass-start current outer-ok)))

;; One universally quantified state of the odd-index pass.

(defun oets-odd-loop-state-p
    (original pass-start current half-index odd-ok)
  (let ((index (+ (* 2 half-index) 1)))
    (and
     (and
      (<= 0 half-index)
      (<= 0 index))
     (oets-permutation-p original current)
     (oets-odd-sorted-p current index)
     (if (equal odd-ok t)
         (equal
          (oets-inversions current)
          (oets-inversions pass-start))
       (<
        (oets-inversions current)
        (oets-inversions pass-start))))))

(defun oets-odd-loop-step-p
    (original pass-start current
              outer-ok half-index odd-ok)
  (let ((index (+ (* 2 half-index) 1)))
    (if (< index (- (len current) 1))
        (let ((next-index (+ index 1)))
          (and
           (and
            (<= 0 next-index)
            (< next-index (len current)))
           (and
            (<= 0 index)
            (< index (len current)))
           (if (<
                (oets-nth-int current next-index)
                (oets-nth-int current index))
               (let ((swap-index (+ index 1)))
                 (and
                  (and
                   (and
                    (<= 0 index)
                    (< index (len current)))
                   (<= 0 swap-index)
                   (< swap-index (len current)))
                  (oets-all-odd-swap-results-p
                   original pass-start current
                   half-index index swap-index)))
             (oets-odd-no-swap-conclusion-p
              original pass-start current
              half-index index odd-ok))))
      (oets-odd-loop-exit-p
       original pass-start current
       odd-ok outer-ok))))

(defun-sk oets-all-odd-loop-states-p
    (original pass-start outer-ok)
  (forall (half-index odd-ok current)
    (implies
     (and
      (integerp half-index)
      (booleanp odd-ok)
      (oets-integer-list-p current))
     (implies
      (equal
       (len current)
       (len pass-start))
      (implies
       (oets-odd-loop-state-p
        original pass-start current
        half-index odd-ok)
       (oets-odd-loop-step-p
        original pass-start current
        outer-ok half-index odd-ok))))))

;; This is the explicit initialization of the odd-index pass in the generated
;; verification condition.

(defun oets-odd-loop-initial-p
    (original pass-start)
  (and
   (and
    (<= 0 0)
    (<= 0 1)
    (equal 1 (+ (* 2 0) 1)))
   (oets-permutation-p original pass-start)
   (oets-odd-sorted-p pass-start 1)
   (implies
    (not t)
    (<
     (oets-inversions pass-start)
     (oets-inversions pass-start)))))

;; Preserve the source universal quantification over both Boolean values and
;; every same-length integer-array state of the outer loop.

(defun-sk oets-outer-loop-continuation-p (original)
  (forall (outer-ok pass-start)
    (implies
     (and
      (booleanp outer-ok)
      (oets-integer-list-p pass-start))
     (implies
      (equal
       (len pass-start)
       (len original))
      (implies
       (and
        (oets-permutation-p
         original pass-start)
        (implies
         (equal outer-ok t)
         (oets-sorted-p pass-start)))
       (if (not (equal outer-ok t))
           (and
            (oets-odd-loop-initial-p
             original pass-start)
            (oets-all-odd-loop-states-p
             original pass-start outer-ok))
         (and
          (oets-sorted-p pass-start)
          (oets-permutation-p
           original pass-start))))))))

;; This predicate is the complete unproved verification condition.

(defun
  ntp4vc-pearl-verifythis-2017-odd-even-transposition-sort-challenge3-odd-even-transposition-sortqtvc-statement
  (array)
  (implies
   (oets-integer-list-p array)
   (and
    (oets-permutation-p array array)
    (oets-outer-loop-continuation-p array))))

(value-triple :itpeval-statement-checked)
:q
