;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/mergesort_array_NaturalMergesort_naturalrecqtvc: the natural
;; mergesort recursive verification condition, preserving sorted runs,
;; subarray permutations, and nested loop continuations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; element type and arbitrary total preorder. The carrier is neither bounded
;; nor enumerated, and every preorder law is explicit in the statement.

(defstub nmr-elt-p (value) t)
(defstub nmr-default () t)
(defstub nmr-le (left right) t)

(defun nmr-elt-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (nmr-elt-p (car xs))
       (nmr-elt-list-p (cdr xs)))
    (equal xs nil)))

(defun-sk nmr-total-preorder-p ()
  (forall (x y z)
    (and
     (implies
      (nmr-elt-p x)
      (nmr-le x x))
     (implies
      (and
       (nmr-elt-p x)
       (nmr-elt-p y)
       (nmr-elt-p z)
       (nmr-le x y)
       (nmr-le y z))
      (nmr-le x z))
     (implies
      (and
       (nmr-elt-p x)
       (nmr-elt-p y))
      (or
       (nmr-le x y)
       (nmr-le y x))))))

(defun nmr-source-context-p ()
  (and
   (nmr-elt-p (nmr-default))
   (nmr-total-preorder-p)))

;; Int.toNat sends negative integers to zero. Source list indexing returns the
;; distinguished inhabitant when the resulting natural index is out of range.

(defun nmr-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun nmr-nth (index xs)
  (let ((natural-index
         (nmr-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      (nmr-default))))

;; These are the source natural-number drop, take, and half-open slice
;; operations.

(defun nmr-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      xs
    (nmr-drop (- count 1) (cdr xs))))

(defun nmr-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      nil
    (cons
     (car xs)
     (nmr-take (- count 1) (cdr xs)))))

(defun nmr-slice (xs lower upper)
  (nmr-take
   (nfix (- (nfix upper)
            (nfix lower)))
   (nmr-drop (nfix lower) xs)))

(defun nmr-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (nmr-remove-first value (cdr xs))))))

(defun nmr-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (nmr-permutation-p
      (cdr left)
      (nmr-remove-first (car left) right)))))

;; List.permut_sub includes endpoint bounds and permutation of the selected
;; half-open slice.

(defun nmr-permut-sub-p
    (left right lower upper)
  (and
   (natp lower)
   (natp upper)
   (equal (len left) (len right))
   (<= lower (len left))
   (<= upper (len left))
   (nmr-permutation-p
    (nmr-slice left lower upper)
    (nmr-slice right lower upper))))

;; List.permut_sub' instead fixes the prefix and suffix and permutes the
;; middle slice; unlike permut_sub, its definition has no endpoint bounds.

(defun nmr-permut-sub-prime-p
    (left right lower upper)
  (and
   (natp lower)
   (natp upper)
   (equal (len left) (len right))
   (equal
    (nmr-slice left 0 lower)
    (nmr-slice right 0 lower))
   (equal
    (nmr-slice left upper (len left))
    (nmr-slice right upper (len left)))
   (nmr-permutation-p
    (nmr-slice left lower upper)
    (nmr-slice right lower upper))))

;; SORTED_SUB retains universal quantification over all mathematical integer
;; indices.

(defun-sk nmr-sorted-sub-p (xs lower upper)
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
      (nmr-le
       (nmr-nth i1 xs)
       (nmr-nth i2 xs))))))

(defun-sk nmr-prefix-unchanged-p
    (new old upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper))
      (equal
       (nmr-nth index new)
       (nmr-nth index old))))))

(defun-sk nmr-unchanged-outside-p
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
       (nmr-nth index new)
       (nmr-nth index old))))))

;; This is the repeated result for the unchanged original list.

(defun nmr-self-result-p
    (a lo k endpoint)
  (and
   (or
    (equal endpoint (len a))
    (and
     (< (+ lo k) endpoint)
     (< endpoint (len a))))
   (nmr-sorted-sub-p a lo endpoint)
   (nmr-permut-sub-prime-p
    a a
    (nmr-int-to-nat lo)
    (len a))))

;; This is the corresponding result for a later list, including equality with
;; the original list before lo.

(defun nmr-progress-result-p
    (original current lo k endpoint)
  (and
   (or
    (equal endpoint (len current))
    (and
     (< (+ lo k) endpoint)
     (< endpoint (len current))))
   (nmr-sorted-sub-p current lo endpoint)
   (nmr-permut-sub-prime-p
    original current
    (nmr-int-to-nat lo)
    (len current))
   (nmr-prefix-unchanged-p
    current original lo)))

;; Every a3 satisfying the merge postcondition is passed through the source's
;; final conditional continuation.

(defun nmr-after-a3-p
    (original a3 lo k i hi n)
  (if (equal hi n)
      (nmr-progress-result-p
       original a3 lo k n)
    (and
     (and
      (< (+ lo (+ i 1)) hi)
      (< hi n))
     (nmr-sorted-sub-p a3 lo hi)
     (nmr-permut-sub-prime-p
      original a3
      (nmr-int-to-nat lo)
      (len a3))
     (nmr-prefix-unchanged-p
      a3 original lo))))

(defun-sk nmr-all-a3-p
    (original a2 lo k i hi n)
  (forall (a3)
    (implies
     (nmr-elt-list-p a3)
     (implies
      (equal (len a3) (len a2))
      (implies
       (and
        (nmr-sorted-sub-p a3 lo hi)
        (nmr-permut-sub-p
         a2 a3
         (nmr-int-to-nat lo)
         (nmr-int-to-nat hi))
        (nmr-unchanged-outside-p
         a3 a2 lo hi))
       (nmr-after-a3-p
        original a3 lo k i hi n))))))

;; This conjunction is the merge precondition and its universal continuation
;; at a discovered endpoint hi.

(defun nmr-hi-conclusion-p
    (original a2 tmp2 lo k i mid hi n)
  (and
   (and
    (<= 0 lo)
    (<= lo mid)
    (<= mid hi)
    (<= hi (len tmp2))
    (equal (len tmp2) (len a2)))
   (nmr-sorted-sub-p a2 lo mid)
   (nmr-sorted-sub-p a2 mid hi)
   (nmr-all-a3-p
    original a2 lo k i hi n)))

(defun-sk nmr-all-hi-p
    (original a1 a2 tmp2 lo k i mid n)
  (forall (hi)
    (implies
     (integerp hi)
     (implies
      (and
       (or
        (equal hi (len a2))
        (and
         (< (+ mid i) hi)
         (< hi (len a2))))
       (nmr-sorted-sub-p a2 mid hi)
       (nmr-permut-sub-prime-p
        a1 a2
        (nmr-int-to-nat mid)
        (len a2))
       (nmr-prefix-unchanged-p
        a2 a1 mid))
      (nmr-hi-conclusion-p
       original a2 tmp2 lo k i mid hi n)))))

;; The source quantifies over every pair a2,tmp2 with the required lengths.

(defun-sk nmr-all-a2-tmp2-p
    (original a1 tmp1 lo k i mid n)
  (forall (a2 tmp2)
    (implies
     (and
      (nmr-elt-list-p a2)
      (nmr-elt-list-p tmp2))
     (implies
      (equal (len a2) (len a1))
      (implies
       (equal (len tmp2) (len tmp1))
       (nmr-all-hi-p
        original a1 a2 tmp2
        lo k i mid n))))))

(defun nmr-i-conclusion-p
    (original a1 tmp1 lo k i mid n)
  (and
   (and
    (<= 0 k)
    (< i k))
   (and
    (<= 0 mid)
    (<= mid (len a1))
    (equal (len a1) (len tmp1)))
   (<= 0 i)
   (nmr-all-a2-tmp2-p
    original a1 tmp1
    lo k i mid n)))

;; This preserves the source's universal loop-index quantifier.

(defun-sk nmr-all-i-p
    (original a1 tmp1 lo k o2 mid n)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (and
        (<= 0 i)
        (<= i o2))
       (and
        (< (+ lo i) mid)
        (< mid n))
       (nmr-sorted-sub-p a1 lo mid)
       (nmr-permut-sub-prime-p
        original a1
        (nmr-int-to-nat lo)
        (len a1))
       (nmr-prefix-unchanged-p
        a1 original lo))
      (nmr-i-conclusion-p
       original a1 tmp1
       lo k i mid n)))))

;; Besides the indexed continuation, each mid,a1,tmp1 triple carries the
;; source's final implication for the endpoint reached after the loop.

(defun nmr-mid-closure-p
    (original a1 tmp1 lo k o2 mid n)
  (and
   (nmr-all-i-p
    original a1 tmp1
    lo k o2 mid n)
   (implies
    (and
     (and
      (< (+ lo (+ o2 1)) mid)
      (< mid n))
     (nmr-sorted-sub-p a1 lo mid)
     (nmr-permut-sub-prime-p
      original a1
      (nmr-int-to-nat lo)
      (len a1))
     (nmr-prefix-unchanged-p
      a1 original lo))
    (nmr-progress-result-p
     original a1 lo k mid))))

(defun-sk nmr-all-mid-p
    (original tmp lo k o2 n)
  (forall (mid a1 tmp1)
    (implies
     (and
      (integerp mid)
      (nmr-elt-list-p a1)
      (nmr-elt-list-p tmp1))
     (implies
      (equal (len a1) (len original))
      (implies
       (equal (len tmp1) (len tmp))
       (nmr-mid-closure-p
        original a1 tmp1
        lo k o2 mid n))))))

(defun nmr-o2-nonnegative-result-p
    (a tmp lo k o1 o2 n)
  (and
   (and
    (and
     (< (+ lo 0) o1)
     (< o1 n))
    (nmr-sorted-sub-p a lo o1)
    (nmr-permut-sub-prime-p
     a a
     (nmr-int-to-nat lo)
     (len a)))
   (nmr-all-mid-p
    a tmp lo k o2 n)))

(defun nmr-o1-nonfinal-case-p
    (a tmp lo k o1 n)
  (let ((o2 (- k 1)))
    (and
     (implies
      (<= 0 (+ o2 1))
      (nmr-o2-nonnegative-result-p
       a tmp lo k o1 o2 n))
     (implies
      (< (+ o2 1) 0)
      (nmr-self-result-p
       a lo k o1)))))

(defun nmr-o1-case-p
    (a tmp lo k o1 n)
  (if (equal o1 n)
      (nmr-self-result-p a lo k n)
    (nmr-o1-nonfinal-case-p
     a tmp lo k o1 n)))

;; Every possible maximal sorted run endpoint o1 is retained.

(defun-sk nmr-all-o1-p
    (a tmp lo k n)
  (forall (o1)
    (implies
     (integerp o1)
     (implies
      (and
       (and
        (< lo o1)
        (<= o1 (len a)))
       (nmr-sorted-sub-p a lo o1)
       (implies
        (< o1 (len a))
        (not
         (nmr-le
          (nmr-nth (- o1 1) a)
          (nmr-nth o1 a)))))
      (nmr-o1-case-p
       a tmp lo k o1 n)))))

(defun nmr-recursive-branch-p
    (a tmp lo k n)
  (and
   (and
    (<= 0 lo)
    (< lo (len a)))
   (nmr-all-o1-p
    a tmp lo k n)))

;; This closed predicate is the complete unproved verification condition.

(defun-sk
    ntp4vc-pearl-mergesort-array-naturalmergesort-naturalrecqtvc-statement
    ()
  (forall (lo a tmp k)
    (implies
     (and
      (nmr-source-context-p)
      (integerp lo)
      (nmr-elt-list-p a)
      (nmr-elt-list-p tmp)
      (integerp k)
      (<= 0 lo)
      (<= lo (len a))
      (equal (len a) (len tmp))
      (<= 0 k))
     (let ((n (len a)))
       (if (<= (- n 1) lo)
           (nmr-self-result-p
            a lo k n)
         (nmr-recursive-branch-p
          a tmp lo k n))))))

(value-triple :itpeval-statement-checked)
:q
