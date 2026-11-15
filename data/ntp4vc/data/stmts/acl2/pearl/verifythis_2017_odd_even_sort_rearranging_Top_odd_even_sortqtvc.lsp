;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2017_odd_even_sort_rearranging_Top_odd_even_sortqtvc:
;; the generated verification condition for odd-even sorting, including
;; permutation, adjacent-order, swap, and entropy invariants. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite ACL2 lists of mathematical integers represent the source
;; arrays without restricting the integer domain.

(defun oes-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (oes-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat maps negative integers to zero, and source list lookup returns
;; the inhabited integer default zero outside the finite list.

(defun oes-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun oes-nth-int (xs index)
  (let ((natural-index
         (oes-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; Source List.set changes an in-range natural index and otherwise leaves the
;; list unchanged.

(defun oes-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (oes-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; This is the source array exchange relation on the valid, distinct indices
;; used by the verification condition.

(defun oes-array-exchange-p
    (old new first second)
  (equal
   new
   (oes-list-set
    (oes-list-set
     old
     (oes-int-to-nat first)
     (oes-nth-int old second))
    (oes-int-to-nat second)
    (oes-nth-int old first))))

;; Recursive deletion gives exact finite multiset permutation for typed lists.

(defun oes-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (oes-permutation-p
      (cdr left)
      (remove1-equal (car left) right)))))

;; The source ghost array_max implementation returns zero on the empty list
;; and the maximum entry on a nonempty list.

(defun oes-array-max-tail (xs current)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      current
    (oes-array-max-tail
     (cdr xs)
     (if (< current (car xs))
         (car xs)
       current))))

(defun oes-array-max (xs)
  (if (consp xs)
      (oes-array-max-tail (cdr xs) (car xs))
    0))

(defun-sk oes-array-max-bound-p (xs maximum)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (<=
       (oes-nth-int xs index)
       maximum)))))

;; These predicates are the source mathematical parity predicates.

(defun oes-odd-p (value)
  (and
   (integerp value)
   (equal (mod value 2) 1)))

(defun oes-even-p (value)
  (and
   (integerp value)
   (equal (mod value 2) 0)))

;; Source sortedness quantifies over every pair of mathematical integer
;; indices in the list interval.

(defun-sk oes-sorted-p (xs)
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
       (oes-nth-int xs first)
       (oes-nth-int xs second))))))

(defun-sk oes-odd-adjacent-through-p (xs upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper)
       (oes-odd-p index))
      (<=
       (oes-nth-int xs index)
       (oes-nth-int xs (+ index 1)))))))

(defun-sk oes-even-adjacent-through-p (xs upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper)
       (oes-even-p index))
      (<=
       (oes-nth-int xs index)
       (oes-nth-int xs (+ index 1)))))))

;; Traversing from index zero computes exactly
;; sum_{0 <= i < len(XS)} i * (M - XS[i]).

(defun oes-entropy-from (xs maximum index)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      0
    (+
     (* index (- maximum (car xs)))
     (oes-entropy-from
      (cdr xs)
      maximum
      (+ index 1)))))

(defun oes-entropy (xs maximum)
  (oes-entropy-from xs maximum 0))

;; Consequences of swapping an out-of-order pair in the odd-index pass.

(defun oes-odd-swap-conclusion-p
    (original pass-start before after index maximum)
  (and
   (<= 0 (- (len before) index))
   (<
    (- (len after) (+ index 2))
    (- (len before) index))
   (oes-permutation-p original after)
   (<= 0 (+ index 2))
   (<= (+ index 2) (len after))
   (oes-odd-p (+ index 2))
   (implies
    (equal nil t)
    (equal
     (oes-entropy after maximum)
     (oes-entropy pass-start maximum)))
   (implies
    (equal nil t)
    (oes-odd-adjacent-through-p
     after (+ index 2)))
   (implies
    (not (equal nil t))
    (<
     (oes-entropy after maximum)
     (oes-entropy pass-start maximum)))))

(defun-sk oes-all-odd-swap-results-p
    (original pass-start before index maximum)
  (forall (after)
    (implies
     (oes-integer-list-p after)
     (implies
      (equal (len after) (len before))
      (implies
       (and
        (oes-array-exchange-p
         before after index (+ index 1))
        (<
         (oes-entropy after maximum)
         (oes-entropy before maximum)))
       (oes-odd-swap-conclusion-p
        original
        pass-start
        before
        after
        index
        maximum))))))

(defun oes-odd-no-swap-conclusion-p
    (original pass-start current index ok maximum)
  (and
   (<= 0 (- (len current) index))
   (<
    (- (len current) (+ index 2))
    (- (len current) index))
   (oes-permutation-p original current)
   (<= 0 (+ index 2))
   (<= (+ index 2) (len current))
   (oes-odd-p (+ index 2))
   (implies
    (equal ok t)
    (equal
     (oes-entropy current maximum)
     (oes-entropy pass-start maximum)))
   (implies
    (equal ok t)
    (oes-odd-adjacent-through-p
     current (+ index 2)))
   (implies
    (not (equal ok t))
    (<
     (oes-entropy current maximum)
     (oes-entropy pass-start maximum)))))

;; Consequences of swapping an out-of-order pair in the even-index pass.

(defun oes-even-swap-conclusion-p
    (original pass-start before after index maximum)
  (and
   (<= 0 (- (len before) index))
   (<
    (- (len after) (+ index 2))
    (- (len before) index))
   (oes-permutation-p original after)
   (<= 0 (+ index 2))
   (<= (+ index 2) (len after))
   (oes-even-p (+ index 2))
   (implies
    (equal nil t)
    (equal
     (oes-entropy after maximum)
     (oes-entropy pass-start maximum)))
   (implies
    (equal nil t)
    (oes-odd-adjacent-through-p
     after (- (len after) 1)))
   (implies
    (equal nil t)
    (oes-even-adjacent-through-p
     after (+ index 2)))
   (implies
    (not (equal nil t))
    (<
     (oes-entropy after maximum)
     (oes-entropy pass-start maximum)))))

(defun-sk oes-all-even-swap-results-p
    (original pass-start before index maximum)
  (forall (after)
    (implies
     (oes-integer-list-p after)
     (implies
      (equal (len after) (len before))
      (implies
       (and
        (oes-array-exchange-p
         before after index (+ index 1))
        (<
         (oes-entropy after maximum)
         (oes-entropy before maximum)))
       (oes-even-swap-conclusion-p
        original
        pass-start
        before
        after
        index
        maximum))))))

(defun oes-even-no-swap-conclusion-p
    (original pass-start current index ok maximum)
  (and
   (<= 0 (- (len current) index))
   (<
    (- (len current) (+ index 2))
    (- (len current) index))
   (oes-permutation-p original current)
   (<= 0 (+ index 2))
   (<= (+ index 2) (len current))
   (oes-even-p (+ index 2))
   (implies
    (equal ok t)
    (equal
     (oes-entropy current maximum)
     (oes-entropy pass-start maximum)))
   (implies
    (equal ok t)
    (oes-odd-adjacent-through-p
     current (- (len current) 1)))
   (implies
    (equal ok t)
    (oes-even-adjacent-through-p
     current (+ index 2)))
   (implies
    (not (equal ok t))
    (<
     (oes-entropy current maximum)
     (oes-entropy pass-start maximum)))))

;; The even-index loop retains the outer-loop boolean and the pass-start
;; array because both occur in the source variant and entropy invariants.

(defun oes-even-loop-invariant-p
    (original pass-start current index ok maximum)
  (and
   (oes-permutation-p original current)
   (<= 0 index)
   (<= index (len current))
   (oes-even-p index)
   (implies
    (equal ok t)
    (equal
     (oes-entropy current maximum)
     (oes-entropy pass-start maximum)))
   (implies
    (equal ok t)
    (oes-odd-adjacent-through-p
     current (- (len current) 1)))
   (implies
    (equal ok t)
    (oes-even-adjacent-through-p
     current index))
   (implies
    (not (equal ok t))
    (<
     (oes-entropy current maximum)
     (oes-entropy pass-start maximum)))))

(defun oes-even-loop-exit-p
    (original pass-start current outer-ok ok maximum)
  (and
   (<=
    0
    (+
     (oes-entropy pass-start maximum)
     (if (equal outer-ok t) 0 1)))
   (<
    (+
     (oes-entropy current maximum)
     (if (equal ok t) 0 1))
    (+
     (oes-entropy pass-start maximum)
     (if (equal outer-ok t) 0 1)))
   (oes-permutation-p original current)
   (implies
    (equal ok t)
    (oes-sorted-p current))))

(defun oes-even-loop-step-p
    (original pass-start current index outer-ok ok maximum)
  (if (< index (- (len current) 1))
      (let ((next (+ index 1)))
        (and
         (<= 0 next)
         (< next (len current))
         (<= 0 index)
         (< index (len current))
         (if (<
              (oes-nth-int current next)
              (oes-nth-int current index))
             (let ((swap-index (+ index 1)))
               (and
                (<
                 (oes-nth-int current swap-index)
                 (oes-nth-int current index))
                (<= 0 index)
                (< index swap-index)
                (< swap-index (len current))
                (oes-all-even-swap-results-p
                 original
                 pass-start
                 current
                 index
                 maximum)))
           (oes-even-no-swap-conclusion-p
            original
            pass-start
            current
            index
            ok
            maximum))))
    (oes-even-loop-exit-p
     original
     pass-start
     current
     outer-ok
     ok
     maximum)))

(defun-sk oes-even-loop-continuation-p
    (original pass-start length-reference outer-ok maximum)
  (forall (index ok current)
    (implies
     (and
      (integerp index)
      (booleanp ok)
      (oes-integer-list-p current))
     (implies
      (equal (len current) (len length-reference))
      (implies
       (oes-even-loop-invariant-p
        original pass-start current index ok maximum)
       (oes-even-loop-step-p
        original
        pass-start
        current
        index
        outer-ok
        ok
        maximum))))))

;; Exiting the odd-index loop establishes the initial even-index invariant and
;; retains the complete universal continuation for the second pass.

(defun oes-odd-loop-exit-p
    (original pass-start current odd-ok outer-ok maximum)
  (and
   (oes-permutation-p original current)
   (<= 0 0)
   (<= 0 (len current))
   (oes-even-p 0)
   (implies
    (equal odd-ok t)
    (equal
     (oes-entropy current maximum)
     (oes-entropy pass-start maximum)))
   (implies
    (equal odd-ok t)
    (oes-odd-adjacent-through-p
     current (- (len current) 1)))
   (implies
    (equal odd-ok t)
    (oes-even-adjacent-through-p current 0))
   (implies
    (not (equal odd-ok t))
    (<
     (oes-entropy current maximum)
     (oes-entropy pass-start maximum)))
   (oes-even-loop-continuation-p
    original
    pass-start
    current
    outer-ok
    maximum)))

(defun oes-odd-loop-invariant-p
    (original pass-start current index ok maximum)
  (and
   (oes-permutation-p original current)
   (<= 0 index)
   (<= index (len current))
   (oes-odd-p index)
   (implies
    (equal ok t)
    (equal
     (oes-entropy current maximum)
     (oes-entropy pass-start maximum)))
   (implies
    (equal ok t)
    (oes-odd-adjacent-through-p current index))
   (implies
    (not (equal ok t))
    (<
     (oes-entropy current maximum)
     (oes-entropy pass-start maximum)))))

(defun oes-odd-loop-step-p
    (original pass-start current index outer-ok ok maximum)
  (if (< index (- (len current) 1))
      (let ((next (+ index 1)))
        (and
         (<= 0 next)
         (< next (len current))
         (<= 0 index)
         (< index (len current))
         (if (<
              (oes-nth-int current next)
              (oes-nth-int current index))
             (let ((swap-index (+ index 1)))
               (and
                (<
                 (oes-nth-int current swap-index)
                 (oes-nth-int current index))
                (<= 0 index)
                (< index swap-index)
                (< swap-index (len current))
                (oes-all-odd-swap-results-p
                 original
                 pass-start
                 current
                 index
                 maximum)))
           (oes-odd-no-swap-conclusion-p
            original
            pass-start
            current
            index
            ok
            maximum))))
    (oes-odd-loop-exit-p
     original
     pass-start
     current
     ok
     outer-ok
     maximum)))

(defun-sk oes-odd-loop-continuation-p
    (original pass-start outer-ok maximum)
  (forall (index ok current)
    (implies
     (and
      (integerp index)
      (booleanp ok)
      (oes-integer-list-p current))
     (implies
      (equal (len current) (len pass-start))
      (implies
       (oes-odd-loop-invariant-p
        original pass-start current index ok maximum)
       (oes-odd-loop-step-p
        original
        pass-start
        current
        index
        outer-ok
        ok
        maximum))))))

(defun oes-odd-loop-initial-p
    (original pass-start maximum)
  (and
   (oes-permutation-p original pass-start)
   (<= 0 1)
   (<= 1 (len pass-start))
   (oes-odd-p 1)
   (oes-odd-adjacent-through-p pass-start 1)
   (implies
    (not t)
    (<
     (oes-entropy pass-start maximum)
     (oes-entropy pass-start maximum)))))

;; Preserve the source universal quantification over every same-length
;; integer-array state and both source Boolean values at the outer loop.

(defun-sk oes-outer-loop-continuation-p
    (original maximum)
  (forall (outer-ok pass-start)
    (implies
     (and
      (booleanp outer-ok)
      (oes-integer-list-p pass-start))
     (implies
      (equal (len pass-start) (len original))
      (implies
       (and
        (oes-permutation-p original pass-start)
        (implies
         (equal outer-ok t)
         (oes-sorted-p pass-start)))
       (if (not (equal outer-ok t))
           (and
            (oes-odd-loop-initial-p
             original pass-start maximum)
            (oes-odd-loop-continuation-p
             original
             pass-start
             outer-ok
             maximum))
         (and
          (oes-sorted-p pass-start)
          (oes-permutation-p
           original pass-start))))))))

;; This predicate is the complete unproved verification condition.

(defun
  ntp4vc-pearl-verifythis-2017-odd-even-sort-rearranging-top-odd-even-sortqtvc-statement
  (array)
  (implies
   (and
    (oes-integer-list-p array)
    (< 0 (len array)))
   (let ((maximum
          (oes-array-max array)))
     (implies
      (oes-array-max-bound-p array maximum)
      (and
       (oes-permutation-p array array)
       (oes-outer-loop-continuation-p
        array maximum))))))

(value-triple :itpeval-statement-checked)
:q
