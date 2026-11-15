;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/edit_distance_EditDistance_distanceqtvc: the dynamic-programming
;; verification condition for computing the minimum insertion/deletion edit
;; distance between two words. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and proper lists represent the source integers and lists.
;; Source Int.toNat sends negative integers to zero, and getElem! on an
;; integer list returns the default integer zero outside its bounds.

(defun ntp4vc-ed-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ntp4vc-ed-integer-list-p (cdr xs)))))

(defun ntp4vc-ed-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ntp4vc-ed-nth-int (index xs)
  (let ((value
         (nth (ntp4vc-ed-int-to-nat index) xs)))
    (if (integerp value)
        value
      0)))

(defun ntp4vc-ed-nth-char (index xs)
  (nth (ntp4vc-ed-int-to-nat index) xs))

;; Source List.set leaves a list unchanged when its natural-number index is
;; out of bounds.

(defun ntp4vc-ed-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (ntp4vc-ed-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; This recursive relation is exactly the source inductive DIST relation:
;; empty words have distance zero; adding a symbol on either side costs one;
;; and adding the same symbol on both sides preserves the distance.

(defun ntp4vc-ed-dist-p (left right distance)
  (declare
   (xargs
    :measure
    (+ (acl2-count left)
       (acl2-count right))))
  (if (and (endp left) (endp right))
      (equal distance 0)
    (or
     (and
      (consp left)
      (ntp4vc-ed-dist-p
       (cdr left) right (- distance 1)))
     (and
      (consp right)
      (ntp4vc-ed-dist-p
       left (cdr right) (- distance 1)))
     (and
      (consp left)
      (consp right)
      (equal (car left) (car right))
      (ntp4vc-ed-dist-p
       (cdr left) (cdr right) distance)))))

(defun-sk ntp4vc-ed-distance-lower-bound-p
    (left right distance)
  (forall (other)
    (implies
     (integerp other)
     (implies
      (ntp4vc-ed-dist-p left right other)
      (<= distance other)))))

(defun ntp4vc-ed-minimal-distance-p
    (left right distance)
  (and
   (integerp distance)
   (true-listp left)
   (true-listp right)
   (ntp4vc-ed-dist-p left right distance)
   (ntp4vc-ed-distance-lower-bound-p
    left right distance)))

;; On every nonnegative index used by the verification condition, NTHCDR is
;; the unique suffix operation satisfying the source suffix_nil and
;; suffix_cons equations.

(defun ntp4vc-ed-suffix (word index)
  (nthcdr (ntp4vc-ed-int-to-nat index) word))

(defun ntp4vc-ed-min-suffix-p
    (word1 word2 index1 index2 distance)
  (ntp4vc-ed-minimal-distance-p
   (ntp4vc-ed-suffix word1 index1)
   (ntp4vc-ed-suffix word2 index2)
   distance))

(defun ntp4vc-ed-in-bounds-p (index xs)
  (and
   (integerp index)
   (<= 0 index)
   (< index (len xs))))

;; Function equality in the source is extensional over all integer arguments.
;; The right side is Function.update at INDEX.

(defun-sk ntp4vc-ed-set-function-equal-p
    (xs index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (ntp4vc-ed-nth-int
       argument
       (ntp4vc-ed-list-set
        xs
        (ntp4vc-ed-int-to-nat index)
        value))
      (if (equal argument index)
          value
        (ntp4vc-ed-nth-int argument xs))))))

(defun-sk ntp4vc-ed-zero-prefix-p (xs upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper))
      (equal
       (ntp4vc-ed-nth-int index xs)
       0)))))

(defun-sk ntp4vc-ed-descending-prefix-p
    (xs word2-length upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper))
      (equal
       (ntp4vc-ed-nth-int index xs)
       (- word2-length index))))))

(defun-sk ntp4vc-ed-row-p
    (word1 word2 row xs word2-length)
  (forall (column)
    (implies
     (integerp column)
     (implies
      (and
       (<= 0 column)
       (<= column word2-length))
      (ntp4vc-ed-min-suffix-p
       word1 word2 row column
       (ntp4vc-ed-nth-int column xs))))))

;; The two quantified portions of an inner-loop invariant.

(defun-sk ntp4vc-ed-segment-ranges-p
    (word1 word2 row word2-length split xs)
  (forall (column)
    (implies
     (integerp column)
     (and
      (implies
       (and
        (< split column)
        (<= column word2-length))
       (ntp4vc-ed-min-suffix-p
        word1 word2 row column
        (ntp4vc-ed-nth-int column xs)))
      (implies
       (and
        (<= 0 column)
        (<= column split))
       (ntp4vc-ed-min-suffix-p
        word1 word2 (+ row 1) column
        (ntp4vc-ed-nth-int column xs)))))))

(defun ntp4vc-ed-segments-p
    (word1 word2 row word2-length split xs old-value)
  (and
   (ntp4vc-ed-segment-ranges-p
    word1 word2 row word2-length split xs)
   (ntp4vc-ed-min-suffix-p
    word1 word2
    (+ row 1)
    (+ split 1)
    old-value)))

;; Consequence of one right-to-left inner-loop iteration.

(defun ntp4vc-ed-inner-column-result-p
    (word1 word2 word2-length row column old-value xs)
  (and
   (ntp4vc-ed-in-bounds-p column xs)
   (ntp4vc-ed-in-bounds-p column word2)
   (ntp4vc-ed-in-bounds-p row word1)
   (if
       (equal
        (ntp4vc-ed-nth-char row word1)
        (ntp4vc-ed-nth-char column word2))
       (and
        (ntp4vc-ed-in-bounds-p column xs)
        (let ((updated
               (ntp4vc-ed-list-set
                xs
                (ntp4vc-ed-int-to-nat column)
                old-value)))
          (implies
           (equal (len updated) (len xs))
           (implies
            (ntp4vc-ed-set-function-equal-p
             xs column old-value)
            (ntp4vc-ed-segments-p
             word1 word2 row word2-length
             (- column 1)
             updated
             (ntp4vc-ed-nth-int column xs))))))
     (let ((next-column (+ column 1)))
       (and
        (ntp4vc-ed-in-bounds-p next-column xs)
        (ntp4vc-ed-in-bounds-p column xs)
        (let* ((new-value
                (+
                 (min
                  (ntp4vc-ed-nth-int column xs)
                  (ntp4vc-ed-nth-int next-column xs))
                 1))
               (updated
                (ntp4vc-ed-list-set
                 xs
                 (ntp4vc-ed-int-to-nat column)
                 new-value)))
          (and
           (ntp4vc-ed-in-bounds-p column xs)
           (implies
            (equal (len updated) (len xs))
            (implies
             (ntp4vc-ed-set-function-equal-p
              xs column new-value)
             (ntp4vc-ed-segments-p
              word1 word2 row word2-length
              (- column 1)
              updated
              (ntp4vc-ed-nth-int column xs)))))))))))

(defun-sk ntp4vc-ed-inner-column-continuation-p
    (word1 word2 word2-length row column-upper old-value xs)
  (forall (column)
    (implies
     (integerp column)
     (implies
      (and
       (<= column column-upper)
       (<= 0 column)
       (ntp4vc-ed-segments-p
        word1 word2 row word2-length
        column xs old-value))
      (ntp4vc-ed-inner-column-result-p
       word1 word2 word2-length
       row column old-value xs)))))

(defun ntp4vc-ed-inner-state-conclusion-p
    (word1 word2 word2-length row column-upper old-value xs)
  (and
   (ntp4vc-ed-inner-column-continuation-p
    word1 word2 word2-length
    row column-upper old-value xs)
   (implies
    (ntp4vc-ed-segments-p
     word1 word2 row word2-length
     -1 xs old-value)
    (ntp4vc-ed-row-p
     word1 word2 row xs word2-length))))

(defun-sk ntp4vc-ed-inner-state-continuation-p
    (word1 word2 word2-length row column-upper initial-xs)
  (forall (old-value xs)
    (implies
     (and
      (integerp old-value)
      (ntp4vc-ed-integer-list-p xs))
     (implies
      (equal (len xs) (len initial-xs))
      (ntp4vc-ed-inner-state-conclusion-p
       word1 word2 word2-length row
       column-upper old-value xs)))))

;; Initialization of the last cell and the complete inner-loop VC for one
;; outer-loop row.

(defun ntp4vc-ed-row-step-result-p
    (word1 word2 word2-length row xs)
  (and
   (ntp4vc-ed-in-bounds-p word2-length xs)
   (ntp4vc-ed-in-bounds-p word2-length xs)
   (let* ((old-value
           (ntp4vc-ed-nth-int word2-length xs))
          (new-value (+ old-value 1))
          (updated
           (ntp4vc-ed-list-set
            xs
            (ntp4vc-ed-int-to-nat word2-length)
            new-value)))
     (and
      (ntp4vc-ed-in-bounds-p word2-length xs)
      (implies
       (equal (len updated) (len xs))
       (implies
        (ntp4vc-ed-set-function-equal-p
         xs word2-length new-value)
        (let ((column-upper (- word2-length 1)))
          (and
           (implies
            (<= -1 column-upper)
            (and
             (ntp4vc-ed-segments-p
              word1 word2 row word2-length
              column-upper updated old-value)
             (ntp4vc-ed-inner-state-continuation-p
              word1 word2 word2-length row
              column-upper updated)))
           (implies
            (< column-upper -1)
            (ntp4vc-ed-row-p
             word1 word2 row
             updated word2-length))))))))))

(defun-sk ntp4vc-ed-row-index-continuation-p
    (word1 word2 word2-length row-upper xs)
  (forall (row)
    (implies
     (integerp row)
     (implies
      (and
       (<= row row-upper)
       (<= 0 row)
       (ntp4vc-ed-row-p
        word1 word2 (+ row 1)
        xs word2-length))
      (ntp4vc-ed-row-step-result-p
       word1 word2 word2-length row xs)))))

(defun ntp4vc-ed-final-result-p (word1 word2 xs)
  (and
   (ntp4vc-ed-in-bounds-p 0 xs)
   (ntp4vc-ed-minimal-distance-p
    (ntp4vc-ed-suffix word1 0)
    (ntp4vc-ed-suffix word2 0)
    (ntp4vc-ed-nth-int 0 xs))))

(defun ntp4vc-ed-row-state-conclusion-p
    (word1 word2 word2-length row-upper xs)
  (and
   (ntp4vc-ed-row-index-continuation-p
    word1 word2 word2-length row-upper xs)
   (implies
    (ntp4vc-ed-row-p
     word1 word2 0 xs word2-length)
    (ntp4vc-ed-final-result-p
     word1 word2 xs))))

(defun-sk ntp4vc-ed-row-state-continuation-p
    (word1 word2 word2-length row-upper initial-xs)
  (forall (xs)
    (implies
     (ntp4vc-ed-integer-list-p xs)
     (implies
      (equal (len xs) (len initial-xs))
      (ntp4vc-ed-row-state-conclusion-p
       word1 word2 word2-length
       row-upper xs)))))

(defun ntp4vc-ed-row-loop-p
    (word1 word2 word1-length word2-length initial-xs)
  (let ((row-upper (- word1-length 1)))
    (and
     (implies
      (<= -1 row-upper)
      (and
       (ntp4vc-ed-row-p
        word1 word2 (+ row-upper 1)
        initial-xs word2-length)
       (ntp4vc-ed-row-state-continuation-p
        word1 word2 word2-length
        row-upper initial-xs)))
     (implies
      (< row-upper -1)
      (ntp4vc-ed-final-result-p
       word1 word2 initial-xs)))))

;; Initialization loop that fills t[i] with |word2|-i.

(defun ntp4vc-ed-initialization-step-result-p
    (word1 word2 word1-length word2-length xs index)
  (declare (ignore word1 word2 word1-length))
  (let* ((new-value (- word2-length index))
         (updated
          (ntp4vc-ed-list-set
           xs
           (ntp4vc-ed-int-to-nat index)
           new-value)))
    (and
     (ntp4vc-ed-in-bounds-p index xs)
     (implies
      (equal (len updated) (len xs))
      (implies
       (ntp4vc-ed-set-function-equal-p
        xs index new-value)
       (ntp4vc-ed-descending-prefix-p
        updated word2-length (+ index 1)))))))

(defun-sk ntp4vc-ed-initialization-index-continuation-p
    (word1 word2 word1-length word2-length xs)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (<= index word2-length)
       (ntp4vc-ed-descending-prefix-p
        xs word2-length index))
      (ntp4vc-ed-initialization-step-result-p
       word1 word2 word1-length
       word2-length xs index)))))

(defun ntp4vc-ed-initialized-state-conclusion-p
    (word1 word2 word1-length word2-length xs)
  (and
   (ntp4vc-ed-initialization-index-continuation-p
    word1 word2 word1-length word2-length xs)
   (implies
    (ntp4vc-ed-descending-prefix-p
     xs word2-length (+ word2-length 1))
    (ntp4vc-ed-row-loop-p
     word1 word2 word1-length
     word2-length xs))))

(defun-sk ntp4vc-ed-initialized-state-continuation-p
    (word1 word2 word1-length word2-length initial-xs)
  (forall (xs)
    (implies
     (ntp4vc-ed-integer-list-p xs)
     (implies
      (equal (len xs) (len initial-xs))
      (ntp4vc-ed-initialized-state-conclusion-p
       word1 word2 word1-length
       word2-length xs)))))

(defun ntp4vc-ed-initial-array-conclusion-p
    (word1 word2 word1-length word2-length xs)
  (and
   (implies
    (<= 0 (+ word2-length 1))
    (and
     (ntp4vc-ed-descending-prefix-p
      xs word2-length 0)
     (ntp4vc-ed-initialized-state-continuation-p
      word1 word2 word1-length
      word2-length xs)))
   (implies
    (< (+ word2-length 1) 0)
    (ntp4vc-ed-row-loop-p
     word1 word2 word1-length
     word2-length xs))))

(defun-sk ntp4vc-ed-initial-array-continuation-p
    (word1 word2 word1-length word2-length)
  (forall (xs)
    (implies
     (ntp4vc-ed-integer-list-p xs)
     (implies
      (and
       (ntp4vc-ed-zero-prefix-p
        xs (+ word2-length 1))
       (equal
        (len xs)
        (+ word2-length 1)))
      (ntp4vc-ed-initial-array-conclusion-p
       word1 word2 word1-length
       word2-length xs)))))

(defun
  ntp4vc-pearl-edit-distance-editdistance-distanceqtvc-statement
  (word1 word2)
  (implies
   (and
    (true-listp word1)
    (true-listp word2))
   (let* ((word1-length (len word1))
          (word2-length (len word2))
          (array-length (+ word2-length 1)))
     (and
      (<= 0 array-length)
      (ntp4vc-ed-initial-array-continuation-p
       word1 word2 word1-length word2-length)))))

(value-triple :itpeval-statement-checked)
:q
