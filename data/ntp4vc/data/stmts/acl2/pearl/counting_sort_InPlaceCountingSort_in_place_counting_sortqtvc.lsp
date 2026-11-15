;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/counting_sort_InPlaceCountingSort_in_place_counting_sortqtvc:
;; the in-place counting-sort verification condition for occurrence counts,
;; sorted prefixes, and permutation preservation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite proper integer lists represent the source integer
;; values and lists. Int.toNat maps negative integers to zero, and getElem!
;; returns the integer default zero outside the list.

(defun ntp4vc-csort-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ntp4vc-csort-integer-list-p (cdr xs)))))

(defun ntp4vc-csort-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ntp4vc-csort-nth-int (index xs)
  (let ((value
         (nth
          (ntp4vc-csort-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; Unlike ACL2's update-nth, source List.set leaves a list unchanged when its
;; natural-number index is out of bounds.

(defun ntp4vc-csort-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (ntp4vc-csort-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; These recursive functions are NumOf.numof specialized to equality and
;; strict comparison: they count satisfying indices in the half-open integer
;; interval [lower, upper).

(defun ntp4vc-csort-numeq (xs value lower upper)
  (declare
   (xargs :measure
          (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if
         (equal
          (ntp4vc-csort-nth-int (- upper 1) xs)
          value)
         1
       0)
     (ntp4vc-csort-numeq
      xs value lower (- upper 1)))))

(defun ntp4vc-csort-numlt (xs value lower upper)
  (declare
   (xargs :measure
          (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (if
         (<
          (ntp4vc-csort-nth-int (- upper 1) xs)
          value)
         1
       0)
     (ntp4vc-csort-numlt
      xs value lower (- upper 1)))))

;; Source predicates over all mathematical integer indices.

(defun-sk ntp4vc-csort-k-values-p (xs k)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i (len xs)))
      (and
       (<= 0 (ntp4vc-csort-nth-int i xs))
       (< (ntp4vc-csort-nth-int i xs) k))))))

(defun-sk ntp4vc-csort-sorted-sub-p (xs lower upper)
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
       (ntp4vc-csort-nth-int i1 xs)
       (ntp4vc-csort-nth-int i2 xs))))))

(defun ntp4vc-csort-sorted-p (xs)
  (ntp4vc-csort-sorted-sub-p xs 0 (len xs)))

(defun-sk ntp4vc-csort-permut-p (left right k)
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal (len left) (len right))
      (implies
       (and
        (<= 0 value)
        (< value k))
       (equal
        (ntp4vc-csort-numeq
         left value 0 (len left))
        (ntp4vc-csort-numeq
         right value 0 (len right))))))))

(defun-sk ntp4vc-csort-zero-list-prefix-p (xs upper)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i upper))
      (equal
       (ntp4vc-csort-nth-int i xs)
       0)))))

(defun-sk ntp4vc-csort-counts-at-p
    (counts original k upper)
  (forall (value)
    (implies
     (integerp value)
     (implies
      (and
       (<= 0 value)
       (< value k))
      (equal
       (ntp4vc-csort-nth-int value counts)
       (ntp4vc-csort-numeq
        original value 0 upper))))))

(defun-sk ntp4vc-csort-prefix-values-lt-p
    (xs upper value)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper))
      (and
       (<= 0 (ntp4vc-csort-nth-int index xs))
       (< (ntp4vc-csort-nth-int index xs)
          value))))))

(defun-sk ntp4vc-csort-prefix-values-le-p
    (xs upper value)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper))
      (and
       (<= 0 (ntp4vc-csort-nth-int index xs))
       (<= (ntp4vc-csort-nth-int index xs)
           value))))))

(defun-sk ntp4vc-csort-prefix-counts-p
    (current original value-limit current-upper original-upper)
  (forall (value)
    (implies
     (integerp value)
     (implies
      (and
       (<= 0 value)
       (< value value-limit))
      (equal
       (ntp4vc-csort-numeq
        current value 0 current-upper)
       (ntp4vc-csort-numeq
        original value 0 original-upper))))))

;; Counting-loop continuation.

(defun ntp4vc-csort-count-step-p
    (original counts k upper index)
  (implies
   (and
    (<= 0 index)
    (<= index upper)
    (ntp4vc-csort-counts-at-p
     counts original k index))
   (and
    (<= 0 index)
    (< index (len original))
    (let ((value
           (ntp4vc-csort-nth-int index original)))
      (and
       (<= 0 value)
       (< value (len counts))
       (let* ((next-count
               (+ (ntp4vc-csort-nth-int value counts) 1))
              (updated
               (ntp4vc-csort-list-set
                counts
                (ntp4vc-csort-int-to-nat value)
                next-count)))
         (and
          (<= 0 value)
          (< value (len counts))
          (implies
           (equal (len updated) (len counts))
           (ntp4vc-csort-counts-at-p
            updated original k (+ index 1))))))))))

(defun-sk ntp4vc-csort-count-continuation-p
    (original counts k upper)
  (forall (index)
    (implies
     (integerp index)
     (ntp4vc-csort-count-step-p
      original counts k upper index))))

;; Sorting-loop invariants for the current value.

(defun ntp4vc-csort-value-invariant-p
    (original current value position)
  (and
   (equal
    position
    (ntp4vc-csort-numlt
     original value 0 (len current)))
   (ntp4vc-csort-sorted-sub-p
    current 0 position)
   (ntp4vc-csort-prefix-values-lt-p
    current position value)
   (ntp4vc-csort-prefix-counts-p
    current original value position (len current))))

(defun ntp4vc-csort-value-invariant-le-p
    (original current value position)
  (and
   (equal
    (- (+ position 1) 1)
    (ntp4vc-csort-numlt
     original value 0 (len current)))
   (ntp4vc-csort-sorted-sub-p
    current 0 position)
   (ntp4vc-csort-prefix-values-le-p
    current position value)
   (ntp4vc-csort-prefix-counts-p
    current original value position (len current))
   (equal
    (ntp4vc-csort-numeq
     current value 0 position)
    (- 1 1))))

(defun ntp4vc-csort-next-value-invariant-p
    (original current value position)
  (and
   (equal
    position
    (ntp4vc-csort-numlt
     original (+ value 1) 0 (len current)))
   (ntp4vc-csort-sorted-sub-p
    current 0 position)
   (ntp4vc-csort-prefix-values-lt-p
    current position (+ value 1))
   (ntp4vc-csort-prefix-counts-p
    current original (+ value 1)
    position (len current))))

;; Inner loop that writes each copy of the current value.

(defun ntp4vc-csort-write-invariant-p
    (original current value position iteration)
  (and
   (equal
    (+ (- position iteration) 1)
    (ntp4vc-csort-numlt
     original value 0 (len current)))
   (ntp4vc-csort-sorted-sub-p
    current 0 position)
   (ntp4vc-csort-prefix-values-le-p
    current position value)
   (ntp4vc-csort-prefix-counts-p
    current original value position (len current))
   (equal
    (ntp4vc-csort-numeq
     current value 0 position)
    (- iteration 1))))

(defun ntp4vc-csort-write-step-p
    (original current value position iteration)
  (implies
   (ntp4vc-csort-write-invariant-p
    original current value position iteration)
   (and
    (<= 0 position)
    (< position (len current))
    (let ((updated
           (ntp4vc-csort-list-set
            current
            (ntp4vc-csort-int-to-nat position)
            value)))
      (implies
       (equal (len updated) (len current))
       (and
        (equal
         (+ (- (+ position 1)
               (+ iteration 1))
            1)
         (ntp4vc-csort-numlt
          original value 0 (len updated)))
        (ntp4vc-csort-sorted-sub-p
         updated 0 (+ position 1))
        (ntp4vc-csort-prefix-values-le-p
         updated (+ position 1) value)
        (ntp4vc-csort-prefix-counts-p
         updated original value
         (+ position 1) (len updated))
        (equal
         (ntp4vc-csort-numeq
          updated value 0 (+ position 1))
         (- (+ iteration 1) 1))))))))

(defun-sk ntp4vc-csort-write-iteration-continuation-p
    (original current value position occurrence-count)
  (forall (iteration)
    (implies
     (integerp iteration)
     (implies
      (and
       (<= 1 iteration)
       (<= iteration occurrence-count))
      (ntp4vc-csort-write-step-p
       original current value position iteration)))))

(defun ntp4vc-csort-write-finished-premise-p
    (original current value position occurrence-count)
  (and
   (equal
    (+ (- position (+ occurrence-count 1)) 1)
    (ntp4vc-csort-numlt
     original value 0 (len current)))
   (ntp4vc-csort-sorted-sub-p
    current 0 position)
   (ntp4vc-csort-prefix-values-le-p
    current position value)
   (ntp4vc-csort-prefix-counts-p
    current original value position (len current))
   (equal
    (ntp4vc-csort-numeq
     current value 0 position)
    (- (+ occurrence-count 1) 1))))

(defun ntp4vc-csort-write-list-conclusion-p
    (original current value position occurrence-count)
  (and
   (ntp4vc-csort-write-iteration-continuation-p
    original current value position occurrence-count)
   (implies
    (ntp4vc-csort-write-finished-premise-p
     original current value position occurrence-count)
    (ntp4vc-csort-next-value-invariant-p
     original current value position))))

(defun-sk ntp4vc-csort-write-list-continuation-p
    (original prior value occurrence-count)
  (forall (position current)
    (implies
     (and
      (integerp position)
      (ntp4vc-csort-integer-list-p current))
     (implies
      (equal (len current) (len prior))
      (ntp4vc-csort-write-list-conclusion-p
       original current value position occurrence-count)))))

(defun ntp4vc-csort-value-step-p
    (original counts current value position)
  (and
   (<= 0 value)
   (< value (len counts))
   (let ((occurrence-count
          (ntp4vc-csort-nth-int value counts)))
     (and
      (implies
       (<= 1 (+ occurrence-count 1))
       (and
        (ntp4vc-csort-value-invariant-le-p
         original current value position)
        (ntp4vc-csort-write-list-continuation-p
         original current value occurrence-count)))
      (implies
       (< (+ occurrence-count 1) 1)
       (ntp4vc-csort-next-value-invariant-p
        original current value position))))))

(defun-sk ntp4vc-csort-value-continuation-p
    (original counts current value-upper position)
  (forall (value)
    (implies
     (integerp value)
     (implies
      (and
       (<= 0 value)
       (<= value value-upper)
       (ntp4vc-csort-value-invariant-p
        original current value position))
      (ntp4vc-csort-value-step-p
       original counts current value position)))))

(defun ntp4vc-csort-output-list-conclusion-p
    (original counts current value-upper position k)
  (and
   (ntp4vc-csort-value-continuation-p
    original counts current value-upper position)
   (implies
    (ntp4vc-csort-value-invariant-p
     original current (+ value-upper 1) position)
    (and
     (ntp4vc-csort-sorted-p current)
     (ntp4vc-csort-permut-p original current k)))))

(defun-sk ntp4vc-csort-output-list-continuation-p
    (original counts value-upper k)
  (forall (position current)
    (implies
     (and
      (integerp position)
      (ntp4vc-csort-integer-list-p current))
     (implies
      (equal (len current) (len original))
      (ntp4vc-csort-output-list-conclusion-p
       original counts current value-upper position k)))))

(defun ntp4vc-csort-sort-loop-p
    (original counts k)
  (let ((value-upper (- k 1)))
    (and
     (implies
      (<= 0 (+ value-upper 1))
      (and
       (equal
        0
        (ntp4vc-csort-numlt
         original 0 0 (len original)))
       (ntp4vc-csort-sorted-sub-p
        original 0 0)
       (ntp4vc-csort-prefix-values-lt-p
        original 0 0)
       (ntp4vc-csort-prefix-counts-p
        original original 0 0 (len original))
       (ntp4vc-csort-output-list-continuation-p
        original counts value-upper k)))
     (implies
      (< (+ value-upper 1) 0)
      (and
       (ntp4vc-csort-sorted-p original)
       (ntp4vc-csort-permut-p
        original original k))))))

;; Continuation after the counting array has been initialized.

(defun ntp4vc-csort-count-array-conclusion-p
    (original current-counts k count-upper)
  (and
   (ntp4vc-csort-count-continuation-p
    original current-counts k count-upper)
   (implies
    (ntp4vc-csort-counts-at-p
     current-counts original k (+ count-upper 1))
    (ntp4vc-csort-sort-loop-p
     original current-counts k))))

(defun-sk ntp4vc-csort-current-counts-continuation-p
    (original initial-counts k count-upper)
  (forall (current-counts)
    (implies
     (ntp4vc-csort-integer-list-p current-counts)
     (implies
      (equal
       (len current-counts)
       (len initial-counts))
      (ntp4vc-csort-count-array-conclusion-p
       original current-counts k count-upper)))))

(defun ntp4vc-csort-initial-counts-conclusion-p
    (original initial-counts k)
  (let ((count-upper (- (len original) 1)))
    (and
     (implies
      (<= 0 (+ count-upper 1))
      (and
       (ntp4vc-csort-counts-at-p
        initial-counts original k 0)
       (ntp4vc-csort-current-counts-continuation-p
        original initial-counts k count-upper)))
     (implies
      (< (+ count-upper 1) 0)
      (ntp4vc-csort-sort-loop-p
       original initial-counts k)))))

(defun-sk ntp4vc-csort-initial-counts-continuation-p
    (original k)
  (forall (initial-counts)
    (implies
     (ntp4vc-csort-integer-list-p initial-counts)
     (implies
      (and
       (ntp4vc-csort-zero-list-prefix-p
        initial-counts k)
       (equal (len initial-counts) k))
      (ntp4vc-csort-initial-counts-conclusion-p
       original initial-counts k)))))

(defun
  ntp4vc-pearl-counting-sort-inplacecountingsort-in-place-counting-sortqtvc-statement
  (original k)
  (implies
   (and
    (ntp4vc-csort-integer-list-p original)
    (integerp k)
    (< 0 k)
    (ntp4vc-csort-k-values-p original k))
   (and
    (<= 0 k)
    (ntp4vc-csort-initial-counts-continuation-p
     original k))))

(value-triple :itpeval-statement-checked)
:q
