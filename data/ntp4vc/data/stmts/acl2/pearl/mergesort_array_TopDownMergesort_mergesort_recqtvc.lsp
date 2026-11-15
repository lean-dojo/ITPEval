;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/mergesort_array_TopDownMergesort_mergesort_recqtvc: the top-down
;; mergesort recursive verification condition for sorted subarrays,
;; subarray permutations, and the two recursive and merge continuations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; element type and arbitrary total preorder. The carrier is neither bounded
;; nor enumerated, and every preorder law is explicit in the statement.

(defstub tdm-elt-p (value) t)
(defstub tdm-default () t)
(defstub tdm-le (left right) t)

(defun tdm-elt-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (tdm-elt-p (car xs))
       (tdm-elt-list-p (cdr xs)))
    (equal xs nil)))

(defun-sk tdm-total-preorder-p ()
  (forall (x y z)
    (and
     (implies
      (tdm-elt-p x)
      (tdm-le x x))
     (implies
      (and
       (tdm-elt-p x)
       (tdm-elt-p y)
       (tdm-elt-p z)
       (tdm-le x y)
       (tdm-le y z))
      (tdm-le x z))
     (implies
      (and
       (tdm-elt-p x)
       (tdm-elt-p y))
      (or
       (tdm-le x y)
       (tdm-le y x))))))

(defun tdm-source-context-p ()
  (and
   (tdm-elt-p (tdm-default))
   (tdm-total-preorder-p)))

;; Integer division is truncated toward zero, matching Lean Int.tdiv and
;; Isabelle cdiv on mathematical integers.

(defun tdm-tdiv (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor
              (abs numerator)
              (abs denominator))))
        (if (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

;; Int.toNat sends negative integers to zero. Source list indexing returns the
;; distinguished inhabitant when the resulting natural index is out of range.

(defun tdm-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun tdm-nth (index xs)
  (let ((natural-index
         (tdm-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      (tdm-default))))

;; These are the source natural-number drop, take, and half-open slice
;; operations.

(defun tdm-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      xs
    (tdm-drop (- count 1) (cdr xs))))

(defun tdm-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      nil
    (cons
     (car xs)
     (tdm-take (- count 1) (cdr xs)))))

(defun tdm-slice (xs lower upper)
  (tdm-take
   (nfix (- (nfix upper)
            (nfix lower)))
   (tdm-drop (nfix lower) xs)))

(defun tdm-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (tdm-remove-first value (cdr xs))))))

(defun tdm-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (tdm-permutation-p
      (cdr left)
      (tdm-remove-first (car left) right)))))

;; List.permut_sub includes endpoint bounds and permutation of the selected
;; half-open slice.

(defun tdm-permut-sub-p
    (left right lower upper)
  (and
   (natp lower)
   (natp upper)
   (equal (len left) (len right))
   (<= lower (len left))
   (<= upper (len left))
   (tdm-permutation-p
    (tdm-slice left lower upper)
    (tdm-slice right lower upper))))

;; List.permut_sub' instead fixes the prefix and suffix and permutes the
;; middle slice; unlike permut_sub, its definition has no endpoint bounds.

(defun tdm-permut-sub-prime-p
    (left right lower upper)
  (and
   (natp lower)
   (natp upper)
   (equal (len left) (len right))
   (equal
    (tdm-slice left 0 lower)
    (tdm-slice right 0 lower))
   (equal
    (tdm-slice left upper (len left))
    (tdm-slice right upper (len left)))
   (tdm-permutation-p
    (tdm-slice left lower upper)
    (tdm-slice right lower upper))))

;; SORTED_SUB retains universal quantification over all mathematical integer
;; indices.

(defun-sk tdm-sorted-sub-p (xs lower upper)
  (forall (i1 i2)
    (implies
     (and
      (integerp i1)
      (integerp i2))
     (implies
      (and
       (<= lower i1)
       (< i1 i2)
       (< i2 upper))
      (tdm-le
       (tdm-nth i1 xs)
       (tdm-nth i2 xs))))))

(defun-sk tdm-unchanged-outside-p
    (new old lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (and
        (<= 0 index)
        (< index lower))
       (and
        (<= upper index)
        (< index (len new))))
      (equal
       (tdm-nth index new)
       (tdm-nth index old))))))

;; Every possible merge output satisfying the source postcondition must
;; establish the final sorted-subarray and original-array permutation result.

(defun-sk tdm-all-merged-results-p
    (original a2 lower upper)
  (forall (a3)
    (implies
     (tdm-elt-list-p a3)
     (implies
      (equal (len a3) (len a2))
      (implies
       (and
        (tdm-sorted-sub-p a3 lower upper)
        (tdm-permut-sub-p
         a2 a3
         (tdm-int-to-nat lower)
         (tdm-int-to-nat upper))
        (tdm-unchanged-outside-p
         a3 a2 lower upper))
       (and
        (tdm-sorted-sub-p a3 lower upper)
        (tdm-permut-sub-prime-p
         original a3
         (tdm-int-to-nat lower)
         (tdm-int-to-nat upper))))))))

(defun tdm-merge-obligations-p
    (original a2 tmp2 lower middle upper)
  (and
   (and
    (<= 0 lower)
    (<= lower middle)
    (<= middle upper)
    (<= upper (len tmp2))
    (equal (len tmp2) (len a2)))
   (tdm-sorted-sub-p a2 lower middle)
   (tdm-sorted-sub-p a2 middle upper)
   (tdm-all-merged-results-p
    original a2 lower upper)))

;; This preserves the universal continuation after the second recursive call.

(defun-sk tdm-all-second-results-p
    (original a1 tmp1 lower middle upper)
  (forall (tmp2 a2)
    (implies
     (and
      (tdm-elt-list-p tmp2)
      (tdm-elt-list-p a2))
     (implies
      (equal (len tmp2) (len tmp1))
      (implies
       (equal (len a2) (len a1))
       (implies
        (and
         (tdm-sorted-sub-p a2 middle upper)
         (tdm-permut-sub-prime-p
          a1 a2
          (tdm-int-to-nat middle)
          (tdm-int-to-nat upper)))
        (tdm-merge-obligations-p
         original a2 tmp2
         lower middle upper)))))))

(defun tdm-second-recursion-conclusion-p
    (original a1 tmp1 lower middle upper)
  (and
   (and
    (<= 0 (- upper lower))
    (< (- upper middle)
       (- upper lower)))
   (and
    (<= 0 middle)
    (<= middle upper)
    (<= upper (len a1))
    (equal (len a1) (len tmp1)))
   (tdm-all-second-results-p
    original a1 tmp1
    lower middle upper)))

;; This preserves the universal continuation after the first recursive call.

(defun-sk tdm-all-first-results-p
    (original tmp lower middle upper)
  (forall (tmp1 a1)
    (implies
     (and
      (tdm-elt-list-p tmp1)
      (tdm-elt-list-p a1))
     (implies
      (equal (len tmp1) (len tmp))
      (implies
       (equal (len a1) (len original))
       (implies
        (and
         (tdm-sorted-sub-p a1 lower middle)
         (tdm-permut-sub-prime-p
          original a1
          (tdm-int-to-nat lower)
          (tdm-int-to-nat middle)))
        (tdm-second-recursion-conclusion-p
         original a1 tmp1
         lower middle upper)))))))

(defun tdm-recursive-branch-p
    (lower upper a tmp)
  (and
   (not (equal 2 0))
   (let ((middle
          (+ lower
             (tdm-tdiv
              (- upper lower)
              2))))
     (and
      (and
       (and
        (<= 0 (- upper lower))
        (< (- middle lower)
           (- upper lower)))
       (and
        (<= 0 lower)
        (<= lower middle)
        (<= middle (len a))
        (equal (len a) (len tmp))))
      (tdm-all-first-results-p
       a tmp lower middle upper)))))

(defun tdm-base-branch-p
    (lower upper a)
  (and
   (tdm-sorted-sub-p a lower upper)
   (tdm-permut-sub-prime-p
    a a
    (tdm-int-to-nat lower)
    (tdm-int-to-nat upper))))

;; This closed predicate is the complete unproved verification condition.

(defun-sk
    ntp4vc-pearl-mergesort-array-topdownmergesort-mergesort-recqtvc-statement
    ()
  (forall (lower upper a tmp)
    (implies
     (and
      (tdm-source-context-p)
      (integerp lower)
      (integerp upper)
      (tdm-elt-list-p a)
      (tdm-elt-list-p tmp)
      (<= 0 lower)
      (<= lower upper)
      (<= upper (len a))
      (equal (len a) (len tmp)))
     (if (<= (- upper 1) lower)
         (tdm-base-branch-p
          lower upper a)
       (tdm-recursive-branch-p
        lower upper a tmp)))))

(value-triple :itpeval-statement-checked)
:q
