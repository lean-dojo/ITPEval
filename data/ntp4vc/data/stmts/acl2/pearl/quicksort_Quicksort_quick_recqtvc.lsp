;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/quicksort_Quicksort_quick_recqtvc: the recursive Bentley-style
;; quicksort verification condition, including partition-loop invariants,
;; swaps, recursively sorted subranges, and subarray permutations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists of integers represent the source
;; integers and integer arrays without restricting either domain.

(defun q1-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (q1-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat sends negative integers to zero.  Source list indexing is total,
;; with the inhabited integer default zero outside the list.

(defun q1-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun q1-nth-int (index xs)
  (let ((natural-index
         (q1-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; Natural-number drop, take, and half-open slice implement the list
;; operations used by List.permut_sub'.

(defun q1-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      xs
    (q1-drop (- count 1) (cdr xs))))

(defun q1-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      nil
    (cons
     (car xs)
     (q1-take (- count 1) (cdr xs)))))

(defun q1-slice (xs lower upper)
  (q1-take
   (nfix (- (nfix upper)
            (nfix lower)))
   (q1-drop (nfix lower) xs)))

(defun q1-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (q1-remove-first value (cdr xs))))))

(defun q1-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (q1-permutation-p
      (cdr left)
      (q1-remove-first (car left) right)))))

;; List.permut_sub' fixes the prefix and suffix and permutes the selected
;; middle slice.  Its source definition imposes no endpoint bounds.

(defun q1-permut-sub-prime-p
    (left right lower upper)
  (and
   (natp lower)
   (natp upper)
   (equal (len left) (len right))
   (equal
    (q1-slice left 0 lower)
    (q1-slice right 0 lower))
   (equal
    (q1-slice left upper (len left))
    (q1-slice right upper (len left)))
   (q1-permutation-p
    (q1-slice left lower upper)
    (q1-slice right lower upper))))

;; This is the finite-list update used to express the Why3 array swap.

(defun q1-list-set (xs index value)
  (declare (xargs :measure (nfix index)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (q1-list-set
        (cdr xs)
        (- index 1)
        value)))))

(defun q1-array-exchange-p
    (old new first second)
  (equal
   new
   (q1-list-set
    (q1-list-set
     old
     (q1-int-to-nat first)
     (q1-nth-int second old))
    (q1-int-to-nat second)
    (q1-nth-int first old))))

;; The source sorted-subarray predicate quantifies over all integer indices,
;; including equal endpoint indices.

(defun-sk q1-sorted-sub1-p (xs lower upper)
  (forall (i1 i2)
    (implies
     (and
      (integerp i1)
      (integerp i2))
     (implies
      (and
       (<= lower i1)
       (<= i1 i2)
       (< i2 upper))
      (<=
       (q1-nth-int i1 xs)
       (q1-nth-int i2 xs))))))

(defun-sk q1-less-half-open-p
    (xs lower upper pivot)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (<
       (q1-nth-int index xs)
       pivot)))))

(defun-sk q1-less-after-lower-p
    (xs lower upper pivot)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (< lower index)
       (<= index upper))
      (<
       (q1-nth-int index xs)
       pivot)))))

(defun-sk q1-greater-equal-open-p
    (xs lower upper pivot)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (< lower index)
       (< index upper))
      (<=
       pivot
       (q1-nth-int index xs))))))

;; The source file defines this partition predicate alongside the VC.

(defun q1-qs-partition-p
    (old current lower middle upper pivot)
  (and
   (q1-permut-sub-prime-p
    old current
    (q1-int-to-nat lower)
    (q1-int-to-nat upper))
   (q1-less-half-open-p
    current lower middle pivot)
   (q1-greater-equal-open-p
    current middle upper pivot)
   (equal
    (q1-nth-int middle current)
    pivot)))

(defun q1-initial-loop-invariant-p
    (array lower upper pivot o2)
  (and
   (equal
    (q1-nth-int lower array)
    pivot)
   (<= lower lower)
   (< lower o2)
   (q1-less-after-lower-p
    array lower lower pivot)
   (q1-greater-equal-open-p
    array lower o2 pivot)
   (q1-permut-sub-prime-p
    array array
    (q1-int-to-nat lower)
    (q1-int-to-nat upper))))

(defun q1-loop-invariant-p
    (original current lower middle index upper pivot o2 o1)
  (and
   (<= o2 index)
   (<= index o1)
   (equal
    (q1-nth-int lower current)
    pivot)
   (<= lower middle)
   (< middle index)
   (q1-less-after-lower-p
    current lower middle pivot)
   (q1-greater-equal-open-p
    current middle index pivot)
   (q1-permut-sub-prime-p
    original current
    (q1-int-to-nat lower)
    (q1-int-to-nat upper))))

(defun q1-next-invariant-p
    (original current lower middle next-index upper pivot)
  (and
   (equal
    (q1-nth-int lower current)
    pivot)
   (<= lower middle)
   (< middle next-index)
   (q1-less-after-lower-p
    current lower middle pivot)
   (q1-greater-equal-open-p
    current middle next-index pivot)
   (q1-permut-sub-prime-p
    original current
    (q1-int-to-nat lower)
    (q1-int-to-nat upper))))

(defun-sk q1-swap-step-continuation-p
    (original current lower middle index upper pivot)
  (forall (swapped)
    (implies
     (q1-integer-list-p swapped)
     (implies
      (equal (len swapped) (len current))
      (implies
       (q1-array-exchange-p
        current swapped index (+ middle 1))
       (q1-next-invariant-p
        original swapped lower (+ middle 1)
        (+ index 1) upper pivot))))))

(defun q1-loop-step-result-p
    (original current lower middle index upper pivot)
  (and
   (<= 0 index)
   (< index (len current))
   (if (< (q1-nth-int index current) pivot)
       (and
        (<= 0 index)
        (< index (len current))
        (<= 0 (+ middle 1))
        (< (+ middle 1) (len current))
        (q1-swap-step-continuation-p
         original current lower middle index upper pivot))
     (q1-next-invariant-p
      original current lower middle
      (+ index 1) upper pivot))))

(defun-sk q1-all-loop-indices-p
    (original current lower middle upper pivot o2 o1)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (q1-loop-invariant-p
       original current lower middle index upper pivot o2 o1)
      (q1-loop-step-result-p
       original current lower middle index upper pivot)))))

(defun q1-loop-exit-invariant-p
    (original current lower middle upper pivot o1)
  (and
   (equal
    (q1-nth-int lower current)
    pivot)
   (<= lower middle)
   (< middle (+ o1 1))
   (q1-less-after-lower-p
    current lower middle pivot)
   (q1-greater-equal-open-p
    current middle (+ o1 1) pivot)
   (q1-permut-sub-prime-p
    original current
    (q1-int-to-nat lower)
    (q1-int-to-nat upper))))

;; The second recursive-call continuation retains every same-length output
;; satisfying the right recursive call's two postconditions.

(defun-sk q1-after-right-recursion-p
    (original after-left lower right-lower upper)
  (forall (after-right)
    (implies
     (q1-integer-list-p after-right)
     (implies
      (equal (len after-right) (len after-left))
      (implies
       (and
        (q1-sorted-sub1-p
         after-right right-lower upper)
        (q1-permut-sub-prime-p
         after-left after-right
         (q1-int-to-nat right-lower)
         (q1-int-to-nat upper)))
       (and
        (q1-sorted-sub1-p
         after-right lower upper)
        (q1-permut-sub-prime-p
         original after-right
         (q1-int-to-nat lower)
         (q1-int-to-nat upper))))))))

;; The first recursive-call continuation retains every same-length output
;; satisfying the left recursive call's two postconditions.

(defun-sk q1-after-left-recursion-p
    (original after-swap lower middle upper)
  (forall (after-left)
    (implies
     (q1-integer-list-p after-left)
     (implies
      (equal (len after-left) (len after-swap))
      (implies
       (and
        (q1-sorted-sub1-p
         after-left lower middle)
        (q1-permut-sub-prime-p
         after-swap after-left
         (q1-int-to-nat lower)
         (q1-int-to-nat middle)))
       (let ((right-lower (+ middle 1)))
         (and
          (<= 0 (- upper lower))
          (<
           (- upper right-lower)
           (- upper lower))
          (<= 0 right-lower)
          (<= right-lower upper)
          (<= upper (len after-left))
          (q1-after-right-recursion-p
           original after-left lower right-lower upper))))))))

(defun-sk q1-pivot-swap-continuation-p
    (original current lower middle upper)
  (forall (after-swap)
    (implies
     (q1-integer-list-p after-swap)
     (implies
      (equal (len after-swap) (len current))
      (implies
       (q1-array-exchange-p
        current after-swap lower middle)
       (and
        (<= 0 (- upper lower))
        (<
         (- middle lower)
         (- upper lower))
        (<= 0 lower)
        (<= lower middle)
        (<= middle (len after-swap))
        (q1-after-left-recursion-p
         original after-swap lower middle upper)))))))

(defun q1-loop-exit-result-p
    (original current lower middle upper)
  (and
   (<= 0 lower)
   (< lower (len current))
   (<= 0 middle)
   (< middle (len current))
   (q1-pivot-swap-continuation-p
    original current lower middle upper)))

(defun-sk q1-all-loop-states-p
    (original lower upper pivot o2 o1)
  (forall (middle current)
    (implies
     (and
      (integerp middle)
      (q1-integer-list-p current))
     (implies
      (equal (len current) (len original))
      (and
       (q1-all-loop-indices-p
        original current lower middle upper pivot o2 o1)
       (implies
        (q1-loop-exit-invariant-p
         original current lower middle upper pivot o1)
        (q1-loop-exit-result-p
         original current lower middle upper)))))))

(defun q1-recursive-branch-p
    (array lower upper)
  (let ((pivot (q1-nth-int lower array))
        (o1 (- upper 1))
        (o2 (+ lower 1)))
    (and
     (<= 0 lower)
     (< lower (len array))
     (and
      (implies
       (<= o2 (+ o1 1))
       (and
        (q1-initial-loop-invariant-p
         array lower upper pivot o2)
        (q1-all-loop-states-p
         array lower upper pivot o2 o1)))
      (implies
       (< (+ o1 1) o2)
       (and
        (<= 0 lower)
        (< lower (len array))
        (q1-pivot-swap-continuation-p
         array array lower lower upper)))))))

;; This predicate is the complete unproved verification condition.

(defun
    ntp4vc-pearl-quicksort-quicksort-quick-recqtvc-statement
    (lower upper array)
  (implies
   (and
    (integerp lower)
    (integerp upper)
    (q1-integer-list-p array)
    (<= 0 lower)
    (<= lower upper)
    (<= upper (len array)))
   (if (< (+ lower 1) upper)
       (q1-recursive-branch-p
        array lower upper)
     (and
      (q1-sorted-sub1-p
       array lower upper)
      (q1-permut-sub-prime-p
       array array
       (q1-int-to-nat lower)
       (q1-int-to-nat upper))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
