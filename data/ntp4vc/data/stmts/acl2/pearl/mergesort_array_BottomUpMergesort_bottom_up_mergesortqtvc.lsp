;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/mergesort_array_BottomUpMergesort_bottom_up_mergesortqtvc: the
;; bottom-up mergesort verification condition for sorted list chunks and
;; permutation preservation across the initialization and merge loops.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; element type and its arbitrary total preorder.  The carrier is neither
;; bounded nor enumerated; all preorder laws remain explicit in the statement.

(defstub bum-elt-p (x) t)
(defstub bum-default () t)
(defstub bum-le (x y) t)

(defun bum-elt-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (bum-elt-p (car xs))
       (bum-elt-list-p (cdr xs)))
    (equal xs nil)))

(defun-sk bum-total-preorder-p ()
  (forall (x y z)
    (and
     (implies
      (bum-elt-p x)
      (bum-le x x))
     (implies
      (and
       (bum-elt-p x)
       (bum-elt-p y)
       (bum-elt-p z)
       (bum-le x y)
       (bum-le y z))
      (bum-le x z))
     (implies
      (and
       (bum-elt-p x)
       (bum-elt-p y))
      (or
       (bum-le x y)
       (bum-le y x))))))

(defun bum-source-context-p ()
  (and
   (bum-elt-p (bum-default))
   (bum-total-preorder-p)))

;; INT.TONAT sends negative integers to zero.  Source list indexing returns
;; the distinguished inhabitant when the resulting natural index is outside
;; the list.

(defun bum-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun bum-nth (index xs)
  (let ((natural-index
         (bum-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      (bum-default))))

(defun bum-int-min (left right)
  (if (<= left right)
      left
    right))

;; These are the source natural-number drop, take, and half-open slice
;; operations used by List.permut_sub.

(defun bum-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      xs
    (bum-drop (- count 1) (cdr xs))))

(defun bum-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      nil
    (cons
     (car xs)
     (bum-take (- count 1) (cdr xs)))))

(defun bum-slice (xs lower upper)
  (bum-take
   (nfix (- (nfix upper)
            (nfix lower)))
   (bum-drop (nfix lower) xs)))

(defun bum-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (bum-remove-first value (cdr xs))))))

(defun bum-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (bum-permutation-p
      (cdr left)
      (bum-remove-first (car left) right)))))

(defun bum-permut-sub-p
    (left right lower upper)
  (and
   (natp lower)
   (natp upper)
   (equal (len left) (len right))
   (<= lower (len left))
   (<= upper (len left))
   (bum-permutation-p
    (bum-slice left lower upper)
    (bum-slice right lower upper))))

;; SORTED_SUB and SORTED quantify over all source integer indices.  The chunk
;; predicate packages the repeated let-bound l = k * step clauses without
;; changing their universal scope.

(defun-sk bum-sorted-sub-p (xs lower upper)
  (forall (i1 i2)
    (implies
     (and
      (integerp i1)
      (integerp i2)
      (<= lower i1)
      (< i1 i2)
      (< i2 upper))
     (bum-le
      (bum-nth i1 xs)
      (bum-nth i2 xs)))))

(defun bum-sorted-p (xs)
  (bum-sorted-sub-p xs 0 (len xs)))

(defun-sk bum-chunks-sorted-p
    (xs step lower upper n)
  (forall (k)
    (implies
     (integerp k)
     (let ((l (* k step)))
       (implies
        (and
         (<= lower l)
         (< l upper))
        (bum-sorted-sub-p
         xs
         l
         (bum-int-min n (+ l step))))))))

(defun-sk bum-pointwise-copy-p (tmp a)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (len tmp)))
     (equal
      (bum-nth index tmp)
      (bum-nth index a)))))

(defun-sk bum-unchanged-outside-p
    (new old lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (or
       (and
        (<= 0 index)
        (< index lower))
       (and
        (<= upper index)
        (< index (len new)))))
     (equal
      (bum-nth index new)
      (bum-nth index old)))))

;; This is the continuation after merging the two sorted chunks
;; [2*i*len, mid) and [mid, hi).

(defun-sk bum-after-merge-p
    (a a1 a2 i len n mid hi)
  (forall (a3)
    (implies
     (bum-elt-list-p a3)
     (implies
      (equal (len a3) (len a2))
      (implies
       (and
        (bum-sorted-sub-p
         a3
         (* 2 i len)
         hi)
        (bum-permut-sub-p
         a2
         a3
         (bum-int-to-nat (* 2 i len))
         (bum-int-to-nat hi))
        (bum-unchanged-outside-p
         a3
         a2
         (* 2 i len)
         hi))
       (and
        (and
         (<= 0
             (- (+ n len)
                (* 2 i len)))
         (< (- (+ n len)
               (+ mid len))
            (- (+ n len)
               (* 2 i len))))
        (and
         (<= 0 (+ mid len))
         (equal
          (+ mid len)
          (* 2 (+ i 1) len)))
        (bum-permutation-p a1 a3)
        (bum-chunks-sorted-p
         a3
         len
         (+ mid len)
         n
         n)
        (bum-chunks-sorted-p
         a3
         (* 2 len)
         0
         (+ mid len)
         n)))))))

(defun bum-merge-branch-p
    (a a1 a2 tmp2 i len n)
  (let* ((mid (+ (* 2 i len) len))
         (hi (bum-int-min n (+ mid len))))
    (and
     (and
      (<= 0 (* 2 i len))
      (<= (* 2 i len) mid)
      (<= mid hi)
      (<= hi (len tmp2))
      (equal (len tmp2) (len a2)))
     (bum-sorted-sub-p
      a2
      (* 2 i len)
      mid)
     (bum-sorted-sub-p a2 mid hi)
     (bum-after-merge-p
      a a1 a2 i len n mid hi))))

(defun bum-finished-inner-loop-p
    (a a2 len n)
  (and
   (and
    (<= 0 (- (* 2 n) len))
    (< (- (* 2 n)
          (* 2 len))
       (- (* 2 n) len)))
   (<= 1 (* 2 len))
   (bum-permutation-p a a2)
   (bum-chunks-sorted-p
    a2
    (* 2 len)
    0
    n
    n)))

(defun bum-inner-case-p
    (a a1 a2 tmp2 i len n)
  (if (< (* 2 i len)
         (- n len))
      (bum-merge-branch-p
       a a1 a2 tmp2 i len n)
    (bum-finished-inner-loop-p
     a a2 len n)))

(defun-sk bum-all-inner-cases-p
    (a a1 tmp1 len n)
  (forall (i tmp2 a2)
    (implies
     (and
      (integerp i)
      (bum-elt-list-p tmp2)
      (bum-elt-list-p a2))
     (implies
      (equal (len tmp2) (len tmp1))
      (implies
       (equal (len a2) (len a1))
       (implies
        (and
         (<= 0 (* 2 i len))
         (bum-permutation-p a1 a2)
         (bum-chunks-sorted-p
          a2
          len
          (* 2 i len)
          n
          n)
         (bum-chunks-sorted-p
          a2
          (* 2 len)
          0
          (* 2 i len)
          n))
        (bum-inner-case-p
         a a1 a2 tmp2 i len n)))))))

(defun bum-active-outer-loop-p
    (a a1 tmp1 len n)
  (and
   (and
    (<= 0 0)
    (equal 0 (* 2 0 len)))
   (bum-permutation-p a1 a1)
   (bum-chunks-sorted-p
    a1 len 0 n n)
   (bum-chunks-sorted-p
    a1 (* 2 len) 0 0 n)
   (bum-all-inner-cases-p
    a a1 tmp1 len n)))

(defun bum-outer-case-p
    (a a1 tmp1 len n)
  (if (< len n)
      (bum-active-outer-loop-p
       a a1 tmp1 len n)
    (and
     (bum-sorted-p a1)
     (bum-permutation-p a a1))))

(defun-sk bum-all-outer-cases-p
    (a tmp n)
  (forall (len tmp1 a1)
    (implies
     (and
      (integerp len)
      (bum-elt-list-p tmp1)
      (bum-elt-list-p a1))
     (implies
      (equal (len tmp1) (len tmp))
      (implies
       (equal (len a1) (len a))
       (implies
        (and
         (<= 1 len)
         (bum-permutation-p a a1)
         (bum-chunks-sorted-p
          a1 len 0 n n))
        (bum-outer-case-p
         a a1 tmp1 len n)))))))

(defun bum-initial-obligations-p
    (a n)
  (and
   (<= 1 1)
   (bum-permutation-p a a)
   (bum-chunks-sorted-p
    a 1 0 n n)))

(defun-sk bum-all-temporary-lists-p (a n)
  (forall (tmp)
    (implies
     (bum-elt-list-p tmp)
     (implies
      (and
       (equal (len tmp) (len a))
       (bum-pointwise-copy-p tmp a))
      (and
       (bum-initial-obligations-p a n)
       (bum-all-outer-cases-p
        a tmp n))))))

;; This closed predicate is the complete unproved verification condition.

(defun-sk
    ntp4vc-pearl-mergesort-array-bottomupmergesort-bottom-up-mergesortqtvc-statement
    ()
  (forall (a)
    (implies
     (and
      (bum-source-context-p)
      (bum-elt-list-p a))
     (let ((n (len a)))
       (bum-all-temporary-lists-p
        a n)))))

(value-triple :itpeval-statement-checked)
:q
