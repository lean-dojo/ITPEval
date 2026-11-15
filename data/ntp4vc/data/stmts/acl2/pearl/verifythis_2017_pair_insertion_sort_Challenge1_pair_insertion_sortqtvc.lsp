;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2017_pair_insertion_sort_Challenge1_pair_insertion_sortqtvc:
;; the generated verification condition for pair insertion sort, including
;; sorted-prefix and permutation invariants for its nested insertion loops.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite lists of ACL2 integers represent the source lists of
;; mathematical integers without bounding either list length or element value.

(defun pis-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (pis-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat is retained for source list writes. Total integer lookup uses the
;; inhabited default zero for every negative or out-of-range index.

(defun pis-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun pis-nth-int (xs index)
  (if (and
       (integerp index)
       (<= 0 index)
       (< index (len xs)))
      (nth index xs)
    0))

;; Source List.set changes an in-range natural index and leaves the list
;; unchanged when the index is out of range.

(defun pis-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (pis-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; Recursive deletion is exact finite multiset permutation.

(defun pis-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (pis-permutation-p
      (cdr left)
      (remove1-equal (car left) right)))))

;; The source order invariants quantify over all mathematical integer indices.

(defun-sk pis-sorted-before-p (xs upper)
  (forall (k l)
    (implies
     (and
      (integerp k)
      (integerp l))
     (implies
      (and
       (<= 0 k)
       (<= k l)
       (< l upper))
      (<=
       (pis-nth-int xs k)
       (pis-nth-int xs l))))))

(defun-sk pis-prefix-gap-ordered-p
    (xs j gap upper)
  (forall (k l)
    (implies
     (and
      (integerp k)
      (integerp l))
     (implies
      (and
       (<= 0 k)
       (<= k j))
      (implies
       (and
        (< (+ j gap) l)
        (< l upper))
       (<=
        (pis-nth-int xs k)
        (pis-nth-int xs l)))))))

(defun-sk pis-suffix-gap-sorted-p
    (xs j gap upper)
  (forall (k l)
    (implies
     (and
      (integerp k)
      (integerp l))
     (implies
      (and
       (< (+ j gap) k)
       (<= k l)
       (< l upper))
      (<=
       (pis-nth-int xs k)
       (pis-nth-int xs l))))))

(defun-sk pis-strict-gap-lower-p
    (xs value j gap upper)
  (forall (l)
    (implies
     (integerp l)
     (implies
      (and
       (< (+ j gap) l)
       (< l upper))
      (< value (pis-nth-int xs l))))))

(defun-sk pis-weak-gap-lower-p
    (xs value j gap upper)
  (forall (l)
    (implies
     (integerp l)
     (implies
      (and
       (< (+ j gap) l)
       (< l upper))
      (<= value (pis-nth-int xs l))))))

;; This is the extensional Function.update equality appearing after every
;; source list update. Its quantifier still ranges over every integer index.

(defun-sk pis-set-function-equal-p
    (xs index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (pis-nth-int
       (pis-list-set
        xs
        (pis-int-to-nat index)
        value)
       argument)
      (if (equal argument index)
          value
        (pis-nth-int xs argument))))))

;; Invariant of the first inner loop, which inserts the larger of the two
;; pending values. Y is reserved for index j+1 and X for index j+2.

(defun pis-first-loop-invariant-p
    (original current i j x y)
  (and
   (<= -1 j)
   (< j i)
   (pis-sorted-before-p current (+ j 1))
   (pis-prefix-gap-ordered-p
    current j 2 (+ i 2))
   (pis-suffix-gap-sorted-p
    current j 2 (+ i 2))
   (pis-strict-gap-lower-p
    current x j 2 (+ i 2))
   (pis-permutation-p
    original
    (pis-list-set
     (pis-list-set
      current
      (pis-int-to-nat (+ j 1))
      y)
     (pis-int-to-nat (+ j 2))
     x))))

;; Invariant of the second inner loop, which inserts the remaining value Y.

(defun pis-second-loop-invariant-p
    (original current i j y)
  (and
   (<= -1 j)
   (< j i)
   (pis-sorted-before-p current (+ j 1))
   (pis-prefix-gap-ordered-p
    current j 1 (+ i 2))
   (pis-suffix-gap-sorted-p
    current j 1 (+ i 2))
   (pis-weak-gap-lower-p
    current y j 1 (+ i 2))
   (pis-permutation-p
    original
    (pis-list-set
     current
     (pis-int-to-nat (+ j 1))
     y))))

;; Completing the second insertion re-establishes the outer invariant at i+2
;; and strictly decreases the outer-loop variant.

(defun pis-pair-outer-step-p
    (original pair-start final i)
  (and
   (<= 0 (- (len pair-start) i))
   (<
    (- (len final) (+ i 2))
    (- (len pair-start) i))
   (<= 0 (+ i 2))
   (<= (+ i 2) (len final))
   (pis-sorted-before-p final (+ i 2))
   (pis-permutation-p original final)))

(defun pis-second-loop-shift-p
    (original current i j y)
  (and
   (<= 0 j)
   (< j (len current))
   (let* ((old-value
           (pis-nth-int current j))
          (update-index
           (+ j 1))
          (shifted
           (pis-list-set
            current
            (pis-int-to-nat update-index)
            old-value)))
     (and
      (<= 0 update-index)
      (< update-index (len current))
      (implies
       (equal (len shifted) (len current))
       (implies
        (pis-set-function-equal-p
         current update-index old-value)
        (and
         (<= 0 j)
         (< (- j 1) j)
         (pis-second-loop-invariant-p
          original shifted i (- j 1) y))))))))

(defun pis-second-loop-finish-p
    (original pair-start current i j y)
  (let* ((update-index
          (+ j 1))
         (final
          (pis-list-set
           current
           (pis-int-to-nat update-index)
           y)))
    (and
     (<= 0 update-index)
     (< update-index (len current))
     (implies
      (equal (len final) (len current))
      (implies
       (pis-set-function-equal-p
        current update-index y)
       (pis-pair-outer-step-p
        original pair-start final i))))))

(defun pis-second-loop-step-p
    (original pair-start current i j y)
  (and
   (implies
    (<= 0 j)
    (and
     (<= 0 j)
     (< j (len current))))
   (if (and
        (<= 0 j)
        (< y (pis-nth-int current j)))
       (pis-second-loop-shift-p
        original current i j y)
     (pis-second-loop-finish-p
      original pair-start current i j y))))

(defun-sk pis-all-second-loop-states-p
    (original pair-start first-finished i y)
  (forall (j current)
    (implies
     (and
      (integerp j)
      (pis-integer-list-p current))
     (implies
      (equal (len current)
             (len first-finished))
      (implies
       (pis-second-loop-invariant-p
        original current i j y)
       (pis-second-loop-step-p
        original
        pair-start
        current
        i
        j
        y))))))

(defun pis-first-loop-shift-p
    (original current i j x y)
  (and
   (<= 0 j)
   (< j (len current))
   (let* ((old-value
           (pis-nth-int current j))
          (update-index
           (+ j 2))
          (shifted
           (pis-list-set
            current
            (pis-int-to-nat update-index)
            old-value)))
     (and
      (<= 0 update-index)
      (< update-index (len current))
      (implies
       (equal (len shifted) (len current))
       (implies
        (pis-set-function-equal-p
         current update-index old-value)
        (and
         (<= 0 j)
         (< (- j 1) j)
         (pis-first-loop-invariant-p
          original shifted i (- j 1) x y))))))))

(defun pis-first-loop-finish-p
    (original pair-start current i j x y)
  (let* ((update-index
          (+ j 2))
         (first-finished
          (pis-list-set
           current
           (pis-int-to-nat update-index)
           x)))
    (and
     (<= 0 update-index)
     (< update-index (len current))
     (implies
      (equal (len first-finished)
             (len current))
      (implies
       (pis-set-function-equal-p
        current update-index x)
       (and
        (pis-second-loop-invariant-p
         original first-finished i j y)
        (pis-all-second-loop-states-p
         original
         pair-start
         first-finished
         i
         y)))))))

(defun pis-first-loop-step-p
    (original pair-start current i j x y)
  (and
   (implies
    (<= 0 j)
    (and
     (<= 0 j)
     (< j (len current))))
   (if (and
        (<= 0 j)
        (< x (pis-nth-int current j)))
       (pis-first-loop-shift-p
        original current i j x y)
     (pis-first-loop-finish-p
      original pair-start current i j x y))))

(defun-sk pis-all-first-loop-states-p
    (original pair-start i x y)
  (forall (j current)
    (implies
     (and
      (integerp j)
      (pis-integer-list-p current))
     (implies
      (equal (len current)
             (len pair-start))
      (implies
       (pis-first-loop-invariant-p
        original current i j x y)
       (pis-first-loop-step-p
        original
        pair-start
        current
        i
        j
        x
        y))))))

;; The pair-processing branch chooses the larger pending value X and the
;; smaller pending value Y exactly as the source conditional does.

(defun pis-pair-branch-p
    (original current i)
  (and
   (<= 0 i)
   (< i (len current))
   (let* ((first-value
           (pis-nth-int current i))
          (second-index
           (+ i 1)))
     (and
      (<= 0 second-index)
      (< second-index (len current))
      (let ((second-value
             (pis-nth-int current second-index)))
        (if (< first-value second-value)
            (and
             (pis-first-loop-invariant-p
              original
              current
              i
              (- i 1)
              second-value
              first-value)
             (pis-all-first-loop-states-p
              original
              current
              i
              second-value
              first-value))
          (and
           (pis-first-loop-invariant-p
            original
            current
            i
            (- i 1)
            first-value
            second-value)
           (pis-all-first-loop-states-p
            original
            current
            i
            first-value
            second-value))))))))

;; Invariant and continuation of the final single-element insertion used when
;; the source list length is odd.

(defun pis-single-loop-invariant-p
    (original current i j y)
  (and
   (<= -1 j)
   (< j i)
   (pis-sorted-before-p current (+ j 1))
   (pis-prefix-gap-ordered-p
    current j 1 (len current))
   (pis-suffix-gap-sorted-p
    current j 1 (len current))
   (pis-strict-gap-lower-p
    current y j 1 (len current))
   (pis-permutation-p
    original
    (pis-list-set
     current
     (pis-int-to-nat (+ j 1))
     y))))

(defun pis-single-loop-shift-p
    (original current i j y)
  (and
   (<= 0 j)
   (< j (len current))
   (let* ((old-value
           (pis-nth-int current j))
          (update-index
           (+ j 1))
          (shifted
           (pis-list-set
            current
            (pis-int-to-nat update-index)
            old-value)))
     (and
      (<= 0 update-index)
      (< update-index (len current))
      (implies
       (equal (len shifted) (len current))
       (implies
        (pis-set-function-equal-p
         current update-index old-value)
        (and
         (<= 0 j)
         (< (- j 1) j)
         (pis-single-loop-invariant-p
          original shifted i (- j 1) y))))))))

(defun pis-single-loop-finish-p
    (original current j y)
  (let* ((update-index
          (+ j 1))
         (final
          (pis-list-set
           current
           (pis-int-to-nat update-index)
           y)))
    (and
     (<= 0 update-index)
     (< update-index (len current))
     (implies
      (equal (len final) (len current))
      (implies
       (pis-set-function-equal-p
        current update-index y)
       (and
        (pis-sorted-before-p final (len final))
        (pis-permutation-p original final)))))))

(defun pis-single-loop-step-p
    (original current i j y)
  (and
   (implies
    (<= 0 j)
    (and
     (<= 0 j)
     (< j (len current))))
   (if (and
        (<= 0 j)
        (< y (pis-nth-int current j)))
       (pis-single-loop-shift-p
        original current i j y)
     (pis-single-loop-finish-p
      original current j y))))

(defun-sk pis-all-single-loop-states-p
    (original single-start i y)
  (forall (j current)
    (implies
     (and
      (integerp j)
      (pis-integer-list-p current))
     (implies
      (equal (len current)
             (len single-start))
      (implies
       (pis-single-loop-invariant-p
        original current i j y)
       (pis-single-loop-step-p
        original current i j y))))))

(defun pis-single-branch-p
    (original current i)
  (and
   (<= 0 i)
   (< i (len current))
   (let ((y (pis-nth-int current i)))
     (and
      (pis-single-loop-invariant-p
       original current i (- i 1) y)
      (pis-all-single-loop-states-p
       original current i y)))))

;; One arbitrary state satisfying the outer-loop invariants must establish
;; the corresponding pair branch, odd-length branch, or final postcondition.

(defun pis-outer-loop-step-p
    (original current i)
  (if (< i (- (len current) 1))
      (pis-pair-branch-p original current i)
    (if (equal i (- (len current) 1))
        (pis-single-branch-p original current i)
      (and
       (pis-sorted-before-p current (len current))
       (pis-permutation-p original current)))))

(defun-sk pis-all-outer-loop-states-p
    (original)
  (forall (i current)
    (implies
     (and
      (integerp i)
      (pis-integer-list-p current))
     (implies
      (equal (len current)
             (len original))
      (implies
       (and
        (<= 0 i)
        (<= i (len current))
        (pis-sorted-before-p current i)
        (pis-permutation-p original current))
       (pis-outer-loop-step-p
        original current i))))))

(defun ntp4vc-pair-insertion-sort-statement (a)
  (implies
   (pis-integer-list-p a)
   (and
    (<= 0 0)
    (<= 0 (len a))
    (pis-sorted-before-p a 0)
    (pis-permutation-p a a)
    (pis-all-outer-loop-states-p a))))

(value-triple :itpeval-statement-checked)
:q
