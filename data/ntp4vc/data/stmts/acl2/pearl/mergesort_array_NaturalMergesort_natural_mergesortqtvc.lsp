;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/mergesort_array_NaturalMergesort_natural_mergesortqtvc: the natural
;; mergesort verification condition for discovering sorted runs, merging
;; adjacent runs, and preserving list permutations through the nested loops.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; element type and arbitrary total preorder.  The carrier is not finite or
;; enumerated, and all preorder laws remain explicit in the statement.

(defstub nms-elt-p (value) t)
(defstub nms-default () t)
(defstub nms-le (left right) t)

(defun nms-elt-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (nms-elt-p (car xs))
       (nms-elt-list-p (cdr xs)))
    (equal xs nil)))

(defun-sk nms-total-preorder-p ()
  (forall (x y z)
    (and
     (implies
      (nms-elt-p x)
      (nms-le x x))
     (implies
      (and
       (nms-elt-p x)
       (nms-elt-p y)
       (nms-elt-p z)
       (nms-le x y)
       (nms-le y z))
      (nms-le x z))
     (implies
      (and
       (nms-elt-p x)
       (nms-elt-p y))
      (or
       (nms-le x y)
       (nms-le y x))))))

(defun nms-source-context-p ()
  (and
   (nms-elt-p (nms-default))
   (nms-total-preorder-p)))

;; Int.toNat sends negative integers to zero.  Source list indexing returns
;; the distinguished inhabitant when the resulting natural index is outside
;; the list.

(defun nms-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun nms-nth (index xs)
  (let ((natural-index
         (nms-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      (nms-default))))

;; These are the source natural-number drop, take, and half-open slice
;; operations used by List.permut_sub.

(defun nms-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      xs
    (nms-drop (- count 1) (cdr xs))))

(defun nms-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      nil
    (cons
     (car xs)
     (nms-take (- count 1) (cdr xs)))))

(defun nms-slice (xs lower upper)
  (nms-take
   (nfix (- (nfix upper)
            (nfix lower)))
   (nms-drop (nfix lower) xs)))

(defun nms-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (nms-remove-first value (cdr xs))))))

(defun nms-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (nms-permutation-p
      (cdr left)
      (nms-remove-first (car left) right)))))

(defun nms-permut-sub-p
    (left right lower upper)
  (and
   (natp lower)
   (natp upper)
   (equal (len left) (len right))
   (<= lower (len left))
   (<= upper (len left))
   (nms-permutation-p
    (nms-slice left lower upper)
    (nms-slice right lower upper))))

;; SORTED_SUB and SORTED retain their universal quantification over all
;; mathematical integer indices.

(defun-sk nms-sorted-sub-p (xs lower upper)
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
      (nms-le
       (nms-nth i1 xs)
       (nms-nth i2 xs))))))

(defun nms-sorted-p (xs)
  (nms-sorted-sub-p xs 0 (len xs)))

(defun-sk nms-pointwise-copy-p (tmp a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len tmp)))
      (equal
       (nms-nth index tmp)
       (nms-nth index a))))))

(defun-sk nms-unchanged-outside-p
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
       (nms-nth index new)
       (nms-nth index old))))))

;; This continuation preserves the source quantifier over every possible
;; merged list a3 satisfying the merge postcondition on [lo, hi).

(defun nms-after-merged-list-case-p
    (a1 a3 lo first-run first-run1 hi n)
  (if (equal lo 0)
      (and
       (and
        (<= 0 (- n lo))
        (< (- n hi)
           (- n lo)))
       (and
        (<= 0 hi)
        (<= hi n))
       (and
        (<= first-run hi)
        (<= hi n))
       (nms-sorted-sub-p a3 0 hi)
       (or
        (equal hi 0)
        (and
         (<= hi hi)
         (< first-run hi)))
       (nms-permutation-p a1 a3))
    (and
     (and
      (<= 0 (- n lo))
      (< (- n hi)
         (- n lo)))
     (and
      (<= 0 hi)
      (<= hi n))
     (and
      (<= first-run first-run1)
      (<= first-run1 n))
     (nms-sorted-sub-p a3 0 first-run1)
     (or
      (equal hi 0)
      (and
       (<= first-run1 hi)
       (< first-run first-run1)))
     (nms-permutation-p a1 a3))))

(defun-sk nms-all-merged-lists-p
    (a1 a2 lo first-run first-run1 hi n)
  (forall (a3)
    (implies
     (nms-elt-list-p a3)
     (implies
      (equal (len a3) (len a2))
      (implies
       (and
        (nms-sorted-sub-p a3 lo hi)
        (nms-permut-sub-p
         a2
         a3
         (nms-int-to-nat lo)
         (nms-int-to-nat hi))
        (nms-unchanged-outside-p
         a3 a2 lo hi))
       (nms-after-merged-list-case-p
        a1 a3 lo first-run first-run1 hi n))))))

;; For each discovered second run endpoint hi, retain both the merge
;; precondition and the universal continuation over all merge outputs.

(defun nms-hi-case-p
    (a1 a2 tmp2 lo first-run first-run1 mid hi n)
  (and
   (and
    (<= 0 lo)
    (<= lo mid)
    (<= mid hi)
    (<= hi (len tmp2))
    (equal (len tmp2) (len a2)))
   (nms-sorted-sub-p a2 lo mid)
   (nms-sorted-sub-p a2 mid hi)
   (nms-all-merged-lists-p
    a1 a2 lo first-run first-run1 hi n)))

(defun-sk nms-all-hi-p
    (a1 a2 tmp2 lo first-run first-run1 mid n)
  (forall (hi)
    (implies
     (integerp hi)
     (implies
      (and
       (and
        (< mid hi)
        (<= hi (len a2)))
       (nms-sorted-sub-p a2 mid hi)
       (implies
        (< hi (len a2))
        (not
         (nms-le
          (nms-nth (- hi 1) a2)
          (nms-nth hi a2)))))
      (nms-hi-case-p
       a1 a2 tmp2 lo first-run first-run1 mid hi n)))))

(defun nms-mid-case-p
    (a a1 a2 tmp2 lo first-run first-run1 mid n)
  (if (equal mid n)
      (if (equal lo 0)
          (and
           (nms-sorted-p a2)
           (nms-permutation-p a a2))
        (and
         (and
          (<= 0 (- n first-run))
          (< (- n first-run1)
             (- n first-run)))
         (and
          (and
           (<= 0 first-run1)
           (<= first-run1 n))
          (nms-sorted-sub-p a2 0 first-run1))
         (nms-permutation-p a a2)))
    (and
     (and
      (<= 0 mid)
      (< mid (len a2)))
     (nms-all-hi-p
      a1 a2 tmp2 lo first-run first-run1 mid n))))

(defun-sk nms-all-mid-p
    (a a1 a2 tmp2 lo first-run first-run1 n)
  (forall (mid)
    (implies
     (integerp mid)
     (implies
      (and
       (and
        (< lo mid)
        (<= mid (len a2)))
       (nms-sorted-sub-p a2 lo mid)
       (implies
        (< mid (len a2))
        (not
         (nms-le
          (nms-nth (- mid 1) a2)
          (nms-nth mid a2)))))
      (nms-mid-case-p
       a a1 a2 tmp2 lo first-run first-run1 mid n)))))

(defun nms-lo-case-p
    (a a1 a2 tmp2 lo first-run first-run1 n)
  (if (< lo (- n 1))
      (and
       (and
        (<= 0 lo)
        (< lo (len a2)))
       (nms-all-mid-p
        a a1 a2 tmp2 lo first-run first-run1 n))
    (and
     (and
      (<= 0 (- n first-run))
      (< (- n first-run1)
         (- n first-run)))
     (and
      (and
       (<= 0 first-run1)
       (<= first-run1 n))
      (nms-sorted-sub-p a2 0 first-run1))
     (nms-permutation-p a a2))))

(defun-sk nms-all-lo-p
    (a a1 tmp1 first-run n)
  (forall (lo first-run1 tmp2 a2)
    (implies
     (and
      (integerp lo)
      (integerp first-run1)
      (nms-elt-list-p tmp2)
      (nms-elt-list-p a2))
     (implies
      (equal (len tmp2) (len tmp1))
      (implies
       (equal (len a2) (len a1))
       (implies
        (and
         (and
          (<= 0 lo)
          (<= lo n))
         (and
          (<= first-run first-run1)
          (<= first-run1 n))
         (nms-sorted-sub-p a2 0 first-run1)
         (or
          (equal lo 0)
          (and
           (<= first-run1 lo)
           (< first-run first-run1)))
         (nms-permutation-p a1 a2))
        (nms-lo-case-p
         a a1 a2 tmp2 lo first-run first-run1 n)))))))

(defun nms-first-run-case-p
    (a a1 tmp1 first-run n)
  (and
   (and
    (and
     (<= 0 0)
     (<= 0 n))
    (and
     (<= first-run first-run)
     (<= first-run n))
    (nms-sorted-sub-p a1 0 first-run)
    (nms-permutation-p a1 a1))
   (nms-all-lo-p
    a a1 tmp1 first-run n)))

(defun-sk nms-all-first-runs-p
    (a tmp n)
  (forall (first-run tmp1 a1)
    (implies
     (and
      (integerp first-run)
      (nms-elt-list-p tmp1)
      (nms-elt-list-p a1))
     (implies
      (equal (len tmp1) (len tmp))
      (implies
       (equal (len a1) (len a))
       (implies
        (and
         (and
          (<= 0 first-run)
          (<= first-run n))
         (nms-sorted-sub-p a1 0 first-run)
         (nms-permutation-p a a1))
        (nms-first-run-case-p
         a a1 tmp1 first-run n)))))))

(defun nms-initial-obligations-p (a n)
  (and
   (and
    (and
     (<= 0 0)
     (<= 0 n))
    (nms-sorted-sub-p a 0 0))
   (nms-permutation-p a a)))

(defun-sk nms-all-temporary-lists-p (a n)
  (forall (tmp)
    (implies
     (nms-elt-list-p tmp)
     (implies
      (and
       (equal (len tmp) (len a))
       (nms-pointwise-copy-p tmp a))
      (and
       (nms-initial-obligations-p a n)
       (nms-all-first-runs-p a tmp n))))))

;; This closed predicate is the complete unproved verification condition.

(defun-sk
    ntp4vc-pearl-mergesort-array-naturalmergesort-natural-mergesortqtvc-statement
    ()
  (forall (a)
    (implies
     (and
      (nms-source-context-p)
      (nms-elt-list-p a))
     (let ((n (len a)))
       (if (<= n 1)
           (and
            (nms-sorted-p a)
            (nms-permutation-p a a))
         (nms-all-temporary-lists-p a n))))))

(value-triple :itpeval-statement-checked)
:q
