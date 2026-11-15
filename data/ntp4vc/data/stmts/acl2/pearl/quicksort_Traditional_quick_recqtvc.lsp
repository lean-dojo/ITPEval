;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/quicksort_Traditional_quick_recqtvc: the traditional quicksort
;; recursive verification condition, including bidirectional partition scans,
;; swaps, recursive sorted subranges, and subarray permutations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists of integers represent the source
;; integers and integer arrays without restricting either domain.

(defun tq-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (tq-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat sends negative integers to zero. Source list indexing is total,
;; with the inhabited integer default zero outside the list.

(defun tq-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun tq-nth-int (index xs)
  (let ((natural-index
         (tq-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; Natural-number drop, take, and half-open slice implement the list
;; operations used by List.permut_sub'.

(defun tq-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      xs
    (tq-drop (- count 1) (cdr xs))))

(defun tq-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      nil
    (cons
     (car xs)
     (tq-take (- count 1) (cdr xs)))))

(defun tq-slice (xs lower upper)
  (tq-take
   (nfix (- (nfix upper)
            (nfix lower)))
   (tq-drop (nfix lower) xs)))

(defun tq-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (tq-remove-first value (cdr xs))))))

(defun tq-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (tq-permutation-p
      (cdr left)
      (tq-remove-first (car left) right)))))

;; List.permut_sub' fixes the prefix and suffix and permutes the selected
;; middle slice. Its source definition imposes no endpoint bounds.

(defun tq-permut-sub-prime-p
    (left right lower upper)
  (and
   (natp lower)
   (natp upper)
   (equal (len left) (len right))
   (equal
    (tq-slice left 0 lower)
    (tq-slice right 0 lower))
   (equal
    (tq-slice left upper (len left))
    (tq-slice right upper (len left)))
   (tq-permutation-p
    (tq-slice left lower upper)
    (tq-slice right lower upper))))

;; This is the finite-list update used to express the Why3 array swap.

(defun tq-list-set (xs index value)
  (declare (xargs :measure (nfix index)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (tq-list-set
        (cdr xs)
        (- index 1)
        value)))))

(defun tq-array-exchange-p
    (old new first second)
  (equal
   new
   (tq-list-set
    (tq-list-set
     old
     (tq-int-to-nat first)
     (tq-nth-int second old))
    (tq-int-to-nat second)
    (tq-nth-int first old))))

;; The source sorted-subarray predicate quantifies over all integer indices,
;; including equal endpoint indices.

(defun-sk tq-sorted-sub1-p (xs lower upper)
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
       (tq-nth-int i1 xs)
       (tq-nth-int i2 xs))))))

;; These predicates retain the four closed/open interval conventions used by
;; the two partition scans.

(defun-sk tq-all-le-closed-p
    (xs lower upper pivot)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (<= index upper))
      (<=
       (tq-nth-int index xs)
       pivot)))))

(defun-sk tq-all-le-half-open-p
    (xs lower upper pivot)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (<=
       (tq-nth-int index xs)
       pivot)))))

(defun-sk tq-all-ge-half-open-p
    (xs lower upper pivot)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (<=
       pivot
       (tq-nth-int index xs))))))

(defun-sk tq-all-ge-open-p
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
       (tq-nth-int index xs))))))

;; The outer-loop invariant is used both at initialization and for every
;; universally quantified loop state.

(defun tq-loop-invariant-p
    (original current lower upper j i pivot)
  (and
   (and
    (<= lower i)
    (< i (- upper 1)))
   (tq-all-le-closed-p
    current lower i pivot)
   (and
    (< lower j)
    (<= j upper))
   (tq-all-ge-half-open-p
    current j upper pivot)
   (tq-permut-sub-prime-p
    original current
    (tq-int-to-nat lower)
    (tq-int-to-nat upper))
   (equal
    (tq-nth-int lower current)
    pivot)))

;; This is the final continuation after the right recursive call.

(defun-sk tq-after-right-recursion-p
    (original after-left lower right-lower upper)
  (forall (after-right)
    (implies
     (tq-integer-list-p after-right)
     (implies
      (equal (len after-right) (len after-left))
      (implies
       (and
        (tq-sorted-sub1-p
         after-right right-lower upper)
        (tq-permut-sub-prime-p
         after-left after-right
         (tq-int-to-nat right-lower)
         (tq-int-to-nat upper)))
       (and
        (tq-sorted-sub1-p
         after-right lower upper)
        (tq-permut-sub-prime-p
         original after-right
         (tq-int-to-nat lower)
         (tq-int-to-nat upper))))))))

;; Every output satisfying the left recursive call's postconditions is passed
;; to the right recursive-call continuation.

(defun-sk tq-after-left-recursion-p
    (original after-swap lower middle upper)
  (forall (after-left)
    (implies
     (tq-integer-list-p after-left)
     (implies
      (equal (len after-left) (len after-swap))
      (implies
       (and
        (tq-sorted-sub1-p
         after-left lower middle)
        (tq-permut-sub-prime-p
         after-swap after-left
         (tq-int-to-nat lower)
         (tq-int-to-nat middle)))
       (let ((right-lower (+ middle 1)))
         (and
          (and
           (<= 0 (- upper lower))
           (<
            (- upper right-lower)
            (- upper lower)))
          (and
           (<= 0 right-lower)
           (<= right-lower upper)
           (<= upper (len after-left)))
          (tq-after-right-recursion-p
           original after-left
           lower right-lower upper))))))))

;; On loop exit, swap the pivot with j and retain every resulting recursive
;; continuation.

(defun-sk tq-finish-swap-continuation-p
    (original current lower upper j1)
  (forall (after-swap)
    (implies
     (tq-integer-list-p after-swap)
     (implies
      (equal (len after-swap) (len current))
      (implies
       (tq-array-exchange-p
        current after-swap lower j1)
       (and
        (and
         (and
          (<= 0 (- upper lower))
          (<
           (- j1 lower)
           (- upper lower)))
         (and
          (<= 0 lower)
          (<= lower j1)
          (<= j1 (len after-swap))))
        (tq-after-left-recursion-p
         original after-swap
         lower j1 upper)))))))

(defun tq-finish-result-p
    (original current lower upper j1)
  (and
   (and
    (and
     (<= 0 lower)
     (< lower (len current)))
    (and
     (<= 0 j1)
     (< j1 (len current))))
   (tq-finish-swap-continuation-p
    original current lower upper j1)))

;; If the scan indices have not crossed, every list produced by swapping i1
;; and j1 must satisfy the next outer-loop invariant and variant decrease.

(defun-sk tq-loop-swap-continuation-p
    (original current lower upper j i i1 j1 pivot)
  (forall (after-swap)
    (implies
     (tq-integer-list-p after-swap)
     (implies
      (equal (len after-swap) (len current))
      (implies
       (tq-array-exchange-p
        current after-swap i1 j1)
       (and
        (and
         (<= 0 (- j i))
         (<
          (- j1 i1)
          (- j i)))
        (and
         (<= lower i1)
         (< i1 (- upper 1)))
        (tq-all-le-closed-p
         after-swap lower i1 pivot)
        (and
         (< lower j1)
         (<= j1 upper))
        (tq-all-ge-half-open-p
         after-swap j1 upper pivot)
        (tq-permut-sub-prime-p
         original after-swap
         (tq-int-to-nat lower)
         (tq-int-to-nat upper))
        (equal
         (tq-nth-int lower after-swap)
         pivot)))))))

(defun tq-loop-swap-result-p
    (original current lower upper j i i1 j1 pivot)
  (and
   (and
    (and
     (<= 0 i1)
     (< i1 (len current)))
    (and
     (<= 0 j1)
     (< j1 (len current))))
   (tq-loop-swap-continuation-p
    original current lower upper
    j i i1 j1 pivot)))

;; This is the state after decrementing the right scan index and continuing
;; because its element remains greater than the pivot.

(defun tq-j-progress-p
    (current lower upper j j1 pivot)
  (and
   (and
    (<= 0 j1)
    (< (- j1 1) j1))
   (and
    (<= lower (- j1 1))
    (< (- j1 1) j))
   (tq-all-ge-open-p
    current (- j1 1) upper pivot)))

;; Preserve the source's nested tests after the right scan reaches j1.

(defun tq-j1-result-p
    (original current lower upper j i i1 j1 pivot)
  (and
   (and
    (<= 0 j1)
    (< j1 (len current)))
   (if (< pivot (tq-nth-int j1 current))
       (if (equal j1 lower)
           (if (<= j1 i1)
               (tq-finish-result-p
                original current lower upper j1)
             (tq-loop-swap-result-p
              original current lower upper
              j i i1 j1 pivot))
         (tq-j-progress-p
          current lower upper j j1 pivot))
     (if (<= j1 i1)
         (tq-finish-result-p
          original current lower upper j1)
       (tq-loop-swap-result-p
        original current lower upper
        j i i1 j1 pivot)))))

(defun-sk tq-all-j1-p
    (original current lower upper j i i1 pivot)
  (forall (j1)
    (implies
     (integerp j1)
     (implies
      (and
       (and
        (<= lower j1)
        (< j1 j))
       (tq-all-ge-open-p
        current j1 upper pivot))
      (tq-j1-result-p
       original current lower upper
       j i i1 j1 pivot)))))

;; Entering the right scan first establishes its decremented-index invariant.

(defun tq-j-scan-p
    (original current lower upper j i i1 pivot)
  (and
   (and
    (and
     (<= lower (- j 1))
     (< (- j 1) j))
    (tq-all-ge-open-p
     current (- j 1) upper pivot))
   (tq-all-j1-p
    original current lower upper
    j i i1 pivot)))

;; This is the state obtained by incrementing i1 and continuing the left scan.

(defun tq-i-progress-p
    (current lower upper i i1 pivot)
  (and
   (and
    (<= 0 (- upper i1))
    (<
     (- upper (+ i1 1))
     (- upper i1)))
   (and
    (< i (+ i1 1))
    (< (+ i1 1) upper))
   (tq-all-le-half-open-p
    current lower (+ i1 1) pivot)))

;; Preserve the source's nested test after the left scan reaches i1.

(defun tq-i1-result-p
    (original current lower upper j i i1 pivot)
  (and
   (and
    (<= 0 i1)
    (< i1 (len current)))
   (if (< (tq-nth-int i1 current) pivot)
       (if (equal i1 (- upper 1))
           (tq-j-scan-p
            original current lower upper
            j i i1 pivot)
         (tq-i-progress-p
          current lower upper i i1 pivot))
     (tq-j-scan-p
      original current lower upper
      j i i1 pivot))))

(defun-sk tq-all-i1-p
    (original current lower upper j i pivot)
  (forall (i1)
    (implies
     (integerp i1)
     (implies
      (and
       (and
        (< i i1)
        (< i1 upper))
       (tq-all-le-half-open-p
        current lower i1 pivot))
      (tq-i1-result-p
       original current lower upper
       j i i1 pivot)))))

;; The first increment of the left scan and every subsequent left-scan state
;; are both required for each outer-loop state.

(defun tq-loop-state-result-p
    (original current lower upper j i pivot)
  (and
   (and
    (and
     (< i (+ i 1))
     (< (+ i 1) upper))
    (tq-all-le-half-open-p
     current lower (+ i 1) pivot))
   (tq-all-i1-p
    original current lower upper
    j i pivot)))

;; Preserve the universal quantifiers over every pair of scan indices and
;; every same-length integer list satisfying the outer-loop invariant.

(defun-sk tq-all-loop-states-p
    (original lower upper pivot)
  (forall (j i current)
    (implies
     (and
      (integerp j)
      (integerp i)
      (tq-integer-list-p current))
     (implies
      (equal (len current) (len original))
      (implies
       (tq-loop-invariant-p
        original current lower upper
        j i pivot)
       (tq-loop-state-result-p
        original current lower upper
        j i pivot))))))

(defun tq-recursive-branch-p
    (array lower upper)
  (let ((pivot (tq-nth-int lower array)))
    (and
     (and
      (<= 0 lower)
      (< lower (len array)))
     (and
      (tq-loop-invariant-p
       array array lower upper
       upper lower pivot)
      (tq-all-loop-states-p
       array lower upper pivot)))))

;; This predicate is the complete unproved verification condition.

(defun
    ntp4vc-pearl-quicksort-traditional-quick-recqtvc-statement
    (lower upper array)
  (implies
   (and
    (integerp lower)
    (integerp upper)
    (tq-integer-list-p array)
    (<= 0 lower)
    (<= lower upper)
    (<= upper (len array)))
   (if (<= upper (+ lower 1))
       (and
        (tq-sorted-sub1-p
         array lower upper)
        (tq-permut-sub-prime-p
         array array
         (tq-int-to-nat lower)
         (tq-int-to-nat upper)))
     (tq-recursive-branch-p
      array lower upper))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
