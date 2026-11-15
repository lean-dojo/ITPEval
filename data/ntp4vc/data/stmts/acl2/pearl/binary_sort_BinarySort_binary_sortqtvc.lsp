;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/binary_sort_BinarySort_binary_sortqtvc: the binary insertion-sort
;; verification condition for sorted prefixes and whole-list permutations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists directly represent the source integer
;; values and lists.  Int.toNat maps every negative integer to zero, while
;; List.get! returns the integer default zero outside the list.

(defun ntp4vc-bsort-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ntp4vc-bsort-integer-list-p (cdr xs)))))

(defun ntp4vc-bsort-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ntp4vc-bsort-nth-int (index xs)
  (let ((value
         (nth
          (ntp4vc-bsort-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

(defun ntp4vc-bsort-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp xs))
      xs
    (ntp4vc-bsort-drop (- count 1) (cdr xs))))

(defun ntp4vc-bsort-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp xs))
      nil
    (cons
     (car xs)
     (ntp4vc-bsort-take (- count 1) (cdr xs)))))

(defun ntp4vc-bsort-slice (xs lower upper)
  (ntp4vc-bsort-take
   (- (nfix upper) (nfix lower))
   (ntp4vc-bsort-drop (nfix lower) xs)))

(defun ntp4vc-bsort-remove-first (value xs)
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (ntp4vc-bsort-remove-first value (cdr xs))))))

(defun ntp4vc-bsort-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (ntp4vc-bsort-permutation-p
      (cdr left)
      (ntp4vc-bsort-remove-first (car left) right)))))

;; This is List.permut_sub': equal total lengths, unchanged prefix and suffix,
;; and a permutation of the half-open slice [lower, upper).

(defun ntp4vc-bsort-permut-sub-prime-p
    (left right lower upper)
  (and
   (equal (len left) (len right))
   (equal
    (ntp4vc-bsort-slice left 0 lower)
    (ntp4vc-bsort-slice right 0 lower))
   (equal
    (ntp4vc-bsort-slice left upper (len left))
    (ntp4vc-bsort-slice right upper (len right)))
   (ntp4vc-bsort-permutation-p
    (ntp4vc-bsort-slice left lower upper)
    (ntp4vc-bsort-slice right lower upper))))

;; Unlike ACL2's update-nth, Lean List.set leaves a list unchanged when its
;; natural-number index is out of bounds.

(defun ntp4vc-bsort-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (ntp4vc-bsort-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; Int.tdiv and Isabelle cdiv truncate the integer quotient toward zero.

(defun ntp4vc-bsort-tdiv (numerator denominator)
  (if
      (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor
              (abs numerator)
              (abs denominator))))
        (if
            (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

;; The following predicates preserve the source's universal quantification
;; over all mathematical integer indices.

(defun-sk ntp4vc-bsort-sorted-prefix-p (xs upper)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j)
      (<= 0 i)
      (<= i j)
      (< j upper))
     (<=
      (ntp4vc-bsort-nth-int i xs)
      (ntp4vc-bsort-nth-int j xs)))))

(defun-sk ntp4vc-bsort-left-of-p (xs upper pivot)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i upper))
     (<= (ntp4vc-bsort-nth-int i xs) pivot))))

(defun-sk ntp4vc-bsort-right-of-p
    (xs lower upper pivot)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= lower i)
      (< i upper))
     (< pivot (ntp4vc-bsort-nth-int i xs)))))

(defun ntp4vc-bsort-search-invariant-p
    (xs left right k pivot)
  (and
   (<= 0 left)
   (<= left right)
   (<= right k)
   (ntp4vc-bsort-left-of-p xs left pivot)
   (ntp4vc-bsort-right-of-p xs right k pivot)))

;; These two relations are the source's specification of the slice shift that
;; produces a2 from a1.

(defun-sk ntp4vc-bsort-outside-shift-equal-p
    (a1 a2 o2 o3)
  (forall (i)
    (implies
     (and
      (integerp i)
      (or
       (and
        (<= 0 i)
        (< i o3))
       (and
        (<= (+ o3 o2) i)
        (< i (len a2)))))
     (equal
      (ntp4vc-bsort-nth-int i a2)
      (ntp4vc-bsort-nth-int i a1)))))

(defun-sk ntp4vc-bsort-shifted-slice-equal-p
    (a1 a2 left o2 o3)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= o3 i)
      (< i (+ o3 o2)))
     (equal
      (ntp4vc-bsort-nth-int i a2)
      (ntp4vc-bsort-nth-int
       (+ left (- i o3))
       a1)))))

;; Array equality is observable only at valid array indices.  Restricting the
;; extensional update law to that domain avoids identifying negative integers
;; with index zero through int-to-nat.

(defun-sk ntp4vc-bsort-set-function-equal-p
    (a2 left pivot)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len a2)))
     (equal
      (ntp4vc-bsort-nth-int
       i
       (ntp4vc-bsort-list-set
        a2
        (ntp4vc-bsort-int-to-nat left)
        pivot))
      (if (equal i left)
          pivot
        (ntp4vc-bsort-nth-int i a2))))))

;; Continuation after shifting [left+1,k] one place to the right and storing
;; the selected value at left.

(defun-sk ntp4vc-bsort-shift-continuation-p
    (original a1 left k pivot)
  (forall (a2)
    (implies
     (ntp4vc-bsort-integer-list-p a2)
     (implies
      (equal (len a2) (len a1))
      (let ((o2 (- k left))
            (o3 (+ left 1)))
        (implies
         (and
          (ntp4vc-bsort-outside-shift-equal-p
           a1 a2 o2 o3)
          (ntp4vc-bsort-shifted-slice-equal-p
           a1 a2 left o2 o3))
         (and
          (<= 0 left)
          (< left (len a2))
          (let ((updated
                 (ntp4vc-bsort-list-set
                  a2
                  (ntp4vc-bsort-int-to-nat left)
                  pivot)))
            (implies
             (equal (len updated) (len a2))
             (implies
              (ntp4vc-bsort-set-function-equal-p
               a2 left pivot)
              (and
               (ntp4vc-bsort-sorted-prefix-p
                updated
                (+ k 1))
               (ntp4vc-bsort-permut-sub-prime-p
                original updated 0 (len updated)))))))))))))

(defun ntp4vc-bsort-search-step-p
    (original a1 k pivot right left)
  (if (< left right)
      (and
       (not (equal 2 0))
       (let ((mid
              (+
               left
               (ntp4vc-bsort-tdiv
                (- right left)
                2))))
         (and
          (<= 0 mid)
          (< mid (len a1))
          (if (< pivot (ntp4vc-bsort-nth-int mid a1))
              (and
               (<= 0 (- right left))
               (< (- mid left) (- right left))
               (ntp4vc-bsort-search-invariant-p
                a1 left mid k pivot))
            (and
             (<= 0 (- right left))
             (< (- right (+ mid 1)) (- right left))
             (ntp4vc-bsort-search-invariant-p
              a1 (+ mid 1) right k pivot))))))
    (let ((o2 (- k left))
          (o3 (+ left 1)))
      (and
       (and
        (<= 0 left)
        (<= 0 o2)
        (<= (+ left o2) (len a1)))
       (<= 0 o3)
       (<= (+ o3 o2) (len a1))
       (ntp4vc-bsort-shift-continuation-p
        original a1 left k pivot)))))

(defun-sk ntp4vc-bsort-search-continuation-p
    (original a1 k pivot)
  (forall (right left)
    (implies
     (and
      (integerp right)
      (integerp left))
     (implies
      (ntp4vc-bsort-search-invariant-p
       a1 left right k pivot)
      (ntp4vc-bsort-search-step-p
       original a1 k pivot right left)))))

(defun ntp4vc-bsort-k-step-p (original a1 k)
  (and
   (<= 0 k)
   (< k (len a1))
   (let ((pivot (ntp4vc-bsort-nth-int k a1)))
     (and
      (ntp4vc-bsort-search-invariant-p
       a1 0 k k pivot)
      (ntp4vc-bsort-search-continuation-p
       original a1 k pivot)))))

(defun-sk ntp4vc-bsort-k-continuation-p
    (original a1 o1)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (<= 1 k)
       (<= k o1)
       (ntp4vc-bsort-sorted-prefix-p a1 k)
       (ntp4vc-bsort-permut-sub-prime-p
        original a1 0 (len a1)))
      (ntp4vc-bsort-k-step-p original a1 k)))))

(defun-sk ntp4vc-bsort-outer-continuation-p
    (original o1)
  (forall (a1)
    (implies
     (ntp4vc-bsort-integer-list-p a1)
     (implies
      (equal (len a1) (len original))
      (and
       (ntp4vc-bsort-k-continuation-p
        original a1 o1)
       (implies
        (and
         (ntp4vc-bsort-sorted-prefix-p
          a1
          (+ o1 1))
         (ntp4vc-bsort-permut-sub-prime-p
          original a1 0 (len a1)))
        (and
         (ntp4vc-bsort-sorted-prefix-p
          a1
          (len a1))
         (ntp4vc-bsort-permut-sub-prime-p
          original a1 0 (len a1)))))))))

(defun ntp4vc-pearl-binary-sort-binarysort-binary-sortqtvc-statement
    (a)
  (implies
   (ntp4vc-bsort-integer-list-p a)
   (let ((o1 (- (len a) 1)))
     (and
      (implies
       (<= 1 (+ o1 1))
       (and
        (ntp4vc-bsort-sorted-prefix-p a 1)
        (ntp4vc-bsort-permut-sub-prime-p
         a a 0 (len a))
        (ntp4vc-bsort-outer-continuation-p
         a o1)))
      (implies
       (< (+ o1 1) 1)
       (and
        (ntp4vc-bsort-sorted-prefix-p
         a
         (len a))
        (ntp4vc-bsort-permut-sub-prime-p
         a a 0 (len a))))))))

(value-triple :itpeval-statement-checked)
:q
