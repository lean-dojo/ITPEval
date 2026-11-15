;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/mergesort_array_Merge_merge_usingqtvc: the merge verification
;; condition for two adjacent sorted list segments, including permutation
;; preservation and the universally quantified copy-and-merge continuations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; element type and arbitrary total preorder.  The carrier is not bounded or
;; enumerated, and every preorder law is explicit in the statement predicate.

(defstub msm-elt-p (value) t)
(defstub msm-default () t)
(defstub msm-le (left right) t)

(defun msm-elt-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (msm-elt-p (car xs))
       (msm-elt-list-p (cdr xs)))
    (equal xs nil)))

(defun-sk msm-total-preorder-p ()
  (forall (x y z)
    (and
     (implies
      (msm-elt-p x)
      (msm-le x x))
     (implies
      (and
       (msm-elt-p x)
       (msm-elt-p y)
       (msm-elt-p z)
       (msm-le x y)
       (msm-le y z))
      (msm-le x z))
     (implies
      (and
       (msm-elt-p x)
       (msm-elt-p y))
      (or
       (msm-le x y)
       (msm-le y x))))))

(defun msm-source-context-p ()
  (and
   (msm-elt-p (msm-default))
   (msm-total-preorder-p)))

;; Int.toNat sends every negative integer to zero.  List getElem! returns the
;; distinguished inhabitant when the resulting natural index is out of range.

(defun msm-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun msm-nth (index xs)
  (let ((natural-index
         (msm-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      (msm-default))))

;; These are the source natural-number drop, take, and half-open slice
;; operations used in List.permut_sub.

(defun msm-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      xs
    (msm-drop (- count 1) (cdr xs))))

(defun msm-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      nil
    (cons
     (car xs)
     (msm-take (- count 1) (cdr xs)))))

(defun msm-slice (xs lower upper)
  (msm-take
   (nfix (- (nfix upper)
            (nfix lower)))
   (msm-drop (nfix lower) xs)))

(defun msm-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (msm-remove-first value (cdr xs))))))

(defun msm-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (msm-permutation-p
      (cdr left)
      (msm-remove-first (car left) right)))))

(defun msm-permut-sub-p
    (left right lower upper)
  (and
   (natp lower)
   (natp upper)
   (equal (len left) (len right))
   (<= lower (len left))
   (<= upper (len left))
   (msm-permutation-p
    (msm-slice left lower upper)
    (msm-slice right lower upper))))

;; SORTED_SUB retains its universal quantification over all mathematical
;; integer indices in the half-open segment.

(defun-sk msm-sorted-sub-p (xs lower upper)
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
      (msm-le
       (msm-nth i1 xs)
       (msm-nth i2 xs))))))

;; These predicates are the two universally quantified equalities imposed on
;; an arbitrary temporary list after copying the segment [lower, lower+span).

(defun-sk msm-unchanged-outside-p
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
       (msm-nth index new)
       (msm-nth index old))))))

(defun-sk msm-copied-segment-p
    (new source lower span)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index (+ lower span)))
      (equal
       (msm-nth index new)
       (msm-nth
        (- (+ lower index) lower)
        source))))))

;; This is the innermost continuation: every list a1 satisfying the merge
;; postcondition relative to tmp1 must satisfy the corresponding postcondition
;; relative to the original list a.

(defun-sk msm-after-merged-list-p
    (a tmp1 lower upper)
  (forall (a1)
    (implies
     (msm-elt-list-p a1)
     (implies
      (equal (len a1) (len a))
      (implies
       (and
        (msm-sorted-sub-p a1 lower upper)
        (msm-permut-sub-p
         tmp1
         a1
         (msm-int-to-nat lower)
         (msm-int-to-nat upper))
        (msm-unchanged-outside-p
         a1 a lower upper))
       (and
        (msm-sorted-sub-p a1 lower upper)
        (msm-permut-sub-p
         a
         a1
         (msm-int-to-nat lower)
         (msm-int-to-nat upper))
        (msm-unchanged-outside-p
         a1 a lower upper)))))))

;; This preserves the source's universal quantifier over every possible tmp1
;; satisfying the copy specification.

(defun-sk msm-after-copy-p
    (lower middle upper tmp a span)
  (forall (tmp1)
    (implies
     (msm-elt-list-p tmp1)
     (implies
      (equal (len tmp1) (len tmp))
      (implies
       (and
        (msm-unchanged-outside-p
         tmp1 tmp lower (+ lower span))
        (msm-copied-segment-p
         tmp1 a lower span))
       (and
        (and
         (<= 0 lower)
         (<= lower middle)
         (<= middle upper)
         (<= upper (len tmp1))
         (equal (len tmp1) (len a)))
        (msm-sorted-sub-p
         tmp1 lower middle)
        (msm-sorted-sub-p
         tmp1 middle upper)
        (msm-after-merged-list-p
         a tmp1 lower upper)))))))

(defun msm-copy-and-merge-branch-p
    (lower middle upper tmp a)
  (let ((span (- upper lower)))
    (and
     (and
      (and
       (<= 0 lower)
       (<= 0 span)
       (<= (+ lower span) (len a)))
      (<= 0 lower)
      (<= (+ lower span) (len tmp)))
     (msm-after-copy-p
      lower middle upper tmp a span))))

(defun msm-ordered-boundary-branch-p
    (lower upper a)
  (and
   (msm-sorted-sub-p a lower upper)
   (msm-permut-sub-p
    a
    a
    (msm-int-to-nat lower)
    (msm-int-to-nat upper))))

(defun msm-active-merge-branch-p
    (lower middle upper tmp a)
  (and
   (<= 0 middle)
   (< middle (len a))
   (let ((previous (- middle 1)))
     (and
      (<= 0 previous)
      (< previous (len a))
      (if (msm-le
           (msm-nth previous a)
           (msm-nth middle a))
          (msm-ordered-boundary-branch-p
           lower upper a)
        (msm-copy-and-merge-branch-p
         lower middle upper tmp a))))))

;; The arguments represent the source theorem's universally quantified typed
;; parameters.  Its total-preorder axioms and seven named facts are all kept
;; as explicit hypotheses of this unproved predicate.

(defun ntp4vc-pearl-mergesort-array-merge-merge-usingqtvc-statement
    (lower middle upper tmp a o1)
  (implies
   (and
    (msm-source-context-p)
    (integerp lower)
    (integerp middle)
    (integerp upper)
    (msm-elt-list-p tmp)
    (msm-elt-list-p a)
    (booleanp o1)
    (<= 0 lower)
    (<= lower middle)
    (<= middle upper)
    (<= upper (len tmp))
    (equal (len tmp) (len a))
    (msm-sorted-sub-p a lower middle)
    (msm-sorted-sub-p a middle upper)
    (if (< lower middle)
        (equal o1
               (if (< middle upper)
                   t
                 nil))
      (equal o1 nil)))
   (if (equal o1 t)
       (msm-active-merge-branch-p
        lower middle upper tmp a)
     (and
      (msm-sorted-sub-p a lower upper)
      (msm-permut-sub-p
       a
       a
       (msm-int-to-nat lower)
       (msm-int-to-nat upper))))))

(value-triple :itpeval-statement-checked)
:q
