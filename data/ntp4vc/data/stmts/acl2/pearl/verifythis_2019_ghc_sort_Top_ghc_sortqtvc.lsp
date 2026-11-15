;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2019_ghc_sort_Top_ghc_sortqtvc: the final GHC-sort
;; verification condition that copying a nondecreasing integer list with the
;; input multiplicities yields a sorted permutation. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite ACL2 integer lists represent Why3 lists and arrays of
;; mathematical integers, without bounding their lengths or element values.

(defun ghc-sort-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (ghc-sort-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat sends negative integers to zero. Source list lookup uses the
;; inhabited integer default zero outside the list; every active lookup in
;; this VC is nevertheless guarded by its original in-bounds condition.

(defun ghc-sort-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun ghc-sort-nth-int (xs index)
  (let ((natural-index
         (ghc-sort-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

(defun ghc-sort-count-occ (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      0
    (+
     (if (equal value (car xs)) 1 0)
     (ghc-sort-count-occ value (cdr xs)))))

;; MAP-OCC is the finite cardinality of the source half-open set of integer
;; indices whose array lookup equals VALUE.

(defun ghc-sort-map-occ-step
    (value xs index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if (equal
          value
          (ghc-sort-nth-int xs index))
         1
       0)
     (ghc-sort-map-occ-step
      value
      xs
      (+ index 1)
      (- remaining 1)))))

(defun ghc-sort-map-occ
    (value xs lower upper)
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (ghc-sort-map-occ-step
       value xs lower (- upper lower))
    0))

;; This recursive predicate is the source Incr.sorted relation on integer
;; lists: each adjacent pair is nondecreasing.

(defun ghc-sort-increasing-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (<= (car xs) (cadr xs))
       (ghc-sort-increasing-list-p
        (cdr xs)))
    t))

;; IntArraySorted.sorted retains its universal pairwise ordering condition on
;; all mathematical integer indices in the full array interval.

(defun-sk ghc-sort-array-sorted-p (xs)
  (forall (i1 i2)
    (implies
     (and
      (integerp i1)
      (integerp i2))
     (implies
      (and
       (<= 0 i1)
       (<= i1 i2)
       (< i2 (len xs)))
      (<=
       (ghc-sort-nth-int xs i1)
       (ghc-sort-nth-int xs i2))))))

;; Finite-list permutation is encoded by repeatedly removing one matching
;; occurrence. This is equivalent to source List.Perm and to equality of all
;; integer multiplicities.

(defun ghc-sort-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (ghc-sort-remove-first
        value (cdr xs))))))

(defun ghc-sort-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (ghc-sort-permutation-p
      (cdr left)
      (ghc-sort-remove-first
       (car left) right)))))

;; The three quantified predicates below preserve the source universal
;; integer scopes for multiplicities, pointwise copying, and the untouched
;; prefix. The prefix bound is literally zero in this VC, as in the source.

(defun-sk ghc-sort-occurrences-match-p
    (array source)
  (forall (x)
    (implies
     (integerp x)
     (equal
      (ghc-sort-map-occ
       x array 0 (len array))
      (ghc-sort-count-occ x source)))))

(defun-sk ghc-sort-pointwise-copy-p
    (destination source)
  (forall (x)
    (implies
     (integerp x)
     (implies
      (and
       (<= 0 x)
       (< x (len destination)))
      (equal
       (ghc-sort-nth-int destination x)
       (ghc-sort-nth-int source (- x 0)))))))

(defun-sk ghc-sort-zero-prefix-unchanged-p
    (destination original)
  (forall (x)
    (implies
     (integerp x)
     (implies
      (and
       (<= 0 x)
       (< x 0))
      (equal
       (ghc-sort-nth-int destination x)
       (ghc-sort-nth-int original x))))))

;; A1 and L remain internal universal quantifiers with the same nested
;; implication structure as the generated Why3 verification condition.

(defun ghc-sort-result-obligation-p
    (a l a1)
  (implies
   (equal (len a1) (len a))
   (implies
    (and
     (ghc-sort-pointwise-copy-p a1 l)
     (ghc-sort-zero-prefix-unchanged-p
      a1 a)
     (ghc-sort-occurrences-match-p
      a1 l))
    (and
     (ghc-sort-array-sorted-p a1)
     (ghc-sort-permutation-p a1 a)))))

(defun-sk ghc-sort-all-results-p (a l)
  (forall (a1)
    (implies
     (ghc-sort-integer-list-p a1)
     (ghc-sort-result-obligation-p
      a l a1))))

(defun ghc-sort-list-obligation-p (a l)
  (implies
   (and
    (ghc-sort-increasing-list-p l)
    (ghc-sort-occurrences-match-p a l)
    (equal (len l) (len a)))
   (and
    (<= 0 0)
    (equal
     (len l)
     (- (len a) 0))
    (ghc-sort-all-results-p a l))))

(defun-sk ghc-sort-all-lists-p (a)
  (forall (l)
    (implies
     (ghc-sort-integer-list-p l)
     (ghc-sort-list-obligation-p a l))))

;; This closed predicate is the complete unproved ghc_sort verification
;; condition, including the source empty-array branch.

(defun-sk
    ntp4vc-pearl-verifythis-2019-ghc-sort-top-ghc-sortqtvc-statement
    ()
  (forall (a)
    (implies
     (ghc-sort-integer-list-p a)
     (if (equal (len a) 0)
         (and
          (ghc-sort-array-sorted-p a)
          (ghc-sort-permutation-p a a))
       (and
        (< 0 (len a))
        (ghc-sort-all-lists-p a))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
