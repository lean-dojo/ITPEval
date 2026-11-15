;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/quicksort_Quicksort3way_quick_recqtvc: the recursive three-way
;; quicksort verification condition, including partition invariants, swaps,
;; recursive sorted subranges, and subarray permutations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists of integers represent the source
;; integers and integer arrays without restricting either domain.

(defun q3-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (q3-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat maps every negative integer to zero.  Integer list indexing is
;; total, with the source's inhabited integer default zero out of range.

(defun q3-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun q3-nth-int (index xs)
  (let ((natural-index
         (q3-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; Natural-number drop, take, and half-open slice implement the list
;; operations used by List.permut_sub'.

(defun q3-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      xs
    (q3-drop (- count 1) (cdr xs))))

(defun q3-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      nil
    (cons
     (car xs)
     (q3-take (- count 1) (cdr xs)))))

(defun q3-slice (xs lower upper)
  (q3-take
   (nfix (- (nfix upper)
            (nfix lower)))
   (q3-drop (nfix lower) xs)))

(defun q3-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (q3-remove-first value (cdr xs))))))

(defun q3-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (q3-permutation-p
      (cdr left)
      (q3-remove-first (car left) right)))))

;; List.permut_sub' fixes the prefix and suffix and permutes the selected
;; middle slice.  Its source definition does not impose endpoint bounds.

(defun q3-permut-sub-prime-p
    (left right lower upper)
  (and
   (natp lower)
   (natp upper)
   (equal (len left) (len right))
   (equal
    (q3-slice left 0 lower)
    (q3-slice right 0 lower))
   (equal
    (q3-slice left upper (len left))
    (q3-slice right upper (len left)))
   (q3-permutation-p
    (q3-slice left lower upper)
    (q3-slice right lower upper))))

;; This is the exact finite-list update used to express the Why3 array swap.

(defun q3-list-set (xs index value)
  (declare (xargs :measure (nfix index)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (q3-list-set
        (cdr xs)
        (- index 1)
        value)))))

(defun q3-array-exchange-p
    (old new first second)
  (equal
   new
   (q3-list-set
    (q3-list-set
     old
     (q3-int-to-nat first)
     (q3-nth-int second old))
    (q3-int-to-nat second)
    (q3-nth-int first old))))

;; The source sorted-subarray predicate quantifies over all integer indices,
;; including equal endpoint indices.

(defun-sk q3-sorted-sub1-p (xs lower upper)
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
       (q3-nth-int i1 xs)
       (q3-nth-int i2 xs))))))

(defun-sk q3-less-band-p
    (xs lower upper pivot)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (<
       (q3-nth-int index xs)
       pivot)))))

(defun-sk q3-equal-band-p
    (xs lower upper pivot)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (q3-nth-int index xs)
       pivot)))))

(defun-sk q3-greater-band-p
    (xs lower upper pivot)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (<
       pivot
       (q3-nth-int index xs))))))

(defun q3-partition-p
    (old current lower middle-left middle-right upper pivot)
  (and
   (q3-permut-sub-prime-p
    old current
    (q3-int-to-nat lower)
    (q3-int-to-nat upper))
   (q3-less-band-p
    current lower middle-left pivot)
   (q3-equal-band-p
    current middle-left middle-right pivot)
   (q3-greater-band-p
    current middle-right upper pivot)))

(defun q3-loop-invariant-p
    (original current lower i middle-left middle-right upper pivot)
  (and
   (<= lower middle-left)
   (< middle-left i)
   (<= i middle-right)
   (<= middle-right upper)
   (q3-less-band-p
    current lower middle-left pivot)
   (q3-equal-band-p
    current middle-left i pivot)
   (q3-greater-band-p
    current middle-right upper pivot)
   (q3-permut-sub-prime-p
    original current
    (q3-int-to-nat lower)
    (q3-int-to-nat upper))))

(defun q3-less-swap-result-p
    (original swapped lower i middle-left middle-right upper pivot)
  (and
   (<= 0 (- middle-right i))
   (<
    (- middle-right (+ i 1))
    (- middle-right i))
   (<= lower (+ middle-left 1))
   (< (+ middle-left 1) (+ i 1))
   (<= (+ i 1) middle-right)
   (<= middle-right upper)
   (q3-less-band-p
    swapped lower (+ middle-left 1) pivot)
   (q3-equal-band-p
    swapped (+ middle-left 1) (+ i 1) pivot)
   (q3-greater-band-p
    swapped middle-right upper pivot)
   (q3-permut-sub-prime-p
    original swapped
    (q3-int-to-nat lower)
    (q3-int-to-nat upper))))

(defun-sk q3-less-swap-continuation-p
    (original current lower i middle-left middle-right upper pivot)
  (forall (swapped)
    (implies
     (q3-integer-list-p swapped)
     (implies
      (equal (len swapped) (len current))
      (implies
       (q3-array-exchange-p
        current swapped middle-left i)
       (q3-less-swap-result-p
        original swapped lower i middle-left middle-right upper pivot))))))

(defun q3-greater-swap-result-p
    (original swapped lower i middle-left middle-right upper pivot)
  (and
   (<= 0 (- middle-right i))
   (<
    (- (- middle-right 1) i)
    (- middle-right i))
   (<= lower middle-left)
   (< middle-left i)
   (<= i (- middle-right 1))
   (<= (- middle-right 1) upper)
   (q3-less-band-p
    swapped lower middle-left pivot)
   (q3-equal-band-p
    swapped middle-left i pivot)
   (q3-greater-band-p
    swapped (- middle-right 1) upper pivot)
   (q3-permut-sub-prime-p
    original swapped
    (q3-int-to-nat lower)
    (q3-int-to-nat upper))))

(defun-sk q3-greater-swap-continuation-p
    (original current lower i middle-left middle-right upper pivot)
  (forall (swapped)
    (implies
     (q3-integer-list-p swapped)
     (implies
      (equal (len swapped) (len current))
      (implies
       (q3-array-exchange-p
        current swapped i (- middle-right 1))
       (q3-greater-swap-result-p
        original swapped lower i middle-left middle-right upper pivot))))))

(defun q3-equal-step-result-p
    (original current lower i middle-left middle-right upper pivot)
  (and
   (<= 0 (- middle-right i))
   (<
    (- middle-right (+ i 1))
    (- middle-right i))
   (<= lower middle-left)
   (< middle-left (+ i 1))
   (<= (+ i 1) middle-right)
   (<= middle-right upper)
   (q3-less-band-p
    current lower middle-left pivot)
   (q3-equal-band-p
    current middle-left (+ i 1) pivot)
   (q3-greater-band-p
    current middle-right upper pivot)
   (q3-permut-sub-prime-p
    original current
    (q3-int-to-nat lower)
    (q3-int-to-nat upper))))

;; The second recursive-call continuation retains the universal output array.

(defun-sk q3-after-right-recursion-p
    (original after-left lower middle-right upper)
  (forall (after-right)
    (implies
     (q3-integer-list-p after-right)
     (implies
      (equal (len after-right) (len after-left))
      (implies
       (and
        (q3-sorted-sub1-p
         after-right middle-right upper)
        (q3-permut-sub-prime-p
         after-left after-right
         (q3-int-to-nat middle-right)
         (q3-int-to-nat upper)))
       (and
        (q3-sorted-sub1-p
         after-right lower upper)
        (q3-permut-sub-prime-p
         original after-right
         (q3-int-to-nat lower)
         (q3-int-to-nat upper))))))))

;; The first recursive-call continuation retains every output satisfying its
;; sortedness and subarray-permutation postconditions.

(defun-sk q3-after-left-recursion-p
    (original current lower middle-left middle-right upper)
  (forall (after-left)
    (implies
     (q3-integer-list-p after-left)
     (implies
      (equal (len after-left) (len current))
      (implies
       (and
        (q3-sorted-sub1-p
         after-left lower middle-left)
        (q3-permut-sub-prime-p
         current after-left
         (q3-int-to-nat lower)
         (q3-int-to-nat middle-left)))
       (and
        (<= 0 (- upper lower))
        (<
         (- upper middle-right)
         (- upper lower))
        (<= 0 middle-right)
        (<= middle-right upper)
        (<= upper (len after-left))
        (q3-after-right-recursion-p
         original after-left lower middle-right upper)))))))

(defun q3-loop-finished-p
    (original current lower middle-left middle-right upper)
  (and
   (<= 0 (- upper lower))
   (<
    (- middle-left lower)
    (- upper lower))
   (<= 0 lower)
   (<= lower middle-left)
   (<= middle-left (len current))
   (q3-after-left-recursion-p
    original current lower middle-left middle-right upper)))

;; This is the complete body for one arbitrary loop state.

(defun q3-loop-state-result-p
    (original current lower i middle-left middle-right upper pivot)
  (if (< i middle-right)
      (and
       (<= 0 i)
       (< i (len current))
       (if (< (q3-nth-int i current) pivot)
           (and
            (<= 0 middle-left)
            (< middle-left (len current))
            (<= 0 i)
            (< i (len current))
            (q3-less-swap-continuation-p
             original current lower i middle-left middle-right upper pivot))
         (and
          (<= 0 i)
          (< i (len current))
          (if (< pivot (q3-nth-int i current))
              (and
               (<= 0 i)
               (< i (len current))
               (<= 0 (- middle-right 1))
               (< (- middle-right 1) (len current))
               (q3-greater-swap-continuation-p
                original current lower i middle-left middle-right upper pivot))
            (q3-equal-step-result-p
             original current lower i middle-left middle-right upper pivot)))))
    (q3-loop-finished-p
     original current lower middle-left middle-right upper)))

;; Preserve the source universal quantifiers over every integer loop index,
;; partition boundary, and same-length integer array satisfying the invariant.

(defun-sk q3-all-loop-states-p
    (original lower upper pivot)
  (forall (i middle-right middle-left current)
    (implies
     (and
      (integerp i)
      (integerp middle-right)
      (integerp middle-left)
      (q3-integer-list-p current))
     (implies
      (equal (len current) (len original))
      (implies
       (q3-loop-invariant-p
        original current lower i middle-left middle-right upper pivot)
       (q3-loop-state-result-p
        original current lower i middle-left middle-right upper pivot))))))

(defun q3-recursive-branch-p
    (array lower upper)
  (let ((pivot (q3-nth-int lower array))
        (initial-index (+ lower 1)))
    (and
     (<= 0 lower)
     (< lower (len array))
     (and
      (q3-loop-invariant-p
       array array lower initial-index lower upper upper pivot)
      (q3-all-loop-states-p
       array lower upper pivot)))))

;; This predicate is the complete unproved verification condition.

(defun
    ntp4vc-pearl-quicksort-quicksort3way-quick-recqtvc-statement
    (lower upper array)
  (implies
   (and
    (integerp lower)
    (integerp upper)
    (q3-integer-list-p array)
    (<= 0 lower)
    (<= lower upper)
    (<= upper (len array)))
   (if (< (+ lower 1) upper)
       (q3-recursive-branch-p
        array lower upper)
     (and
      (q3-sorted-sub1-p
       array lower upper)
      (q3-permut-sub-prime-p
       array array
       (q3-int-to-nat lower)
       (q3-int-to-nat upper))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
