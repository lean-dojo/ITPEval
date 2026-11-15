;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2019_ghc_sort_Top_copy_listqtvc: the verification
;; condition for copying an integer list into an integer-list array segment
;; while preserving values, the untouched prefix, and occurrence counts.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite lists of ACL2 integers represent the source lists of
;; mathematical integers without bounding their lengths or element values.

(defun cls-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (cls-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat is retained for source list writes. Total integer lookup returns
;; the inhabited default zero for every negative or out-of-range index.

(defun cls-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun cls-nth-int (xs index)
  (if (and
       (integerp index)
       (<= 0 index)
       (< index (len xs)))
      (nth index xs)
    0))

;; This is exactly List.set: an in-range natural index is replaced, while an
;; out-of-range index leaves the proper list unchanged.

(defun cls-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (cls-list-set
        (cdr xs)
        (- index 1)
        value)))))

(defun cls-count-occ (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      0
    (+
     (if (equal value (car xs)) 1 0)
     (cls-count-occ value (cdr xs)))))

;; MAP-OCC-STEP counts the values at REMAINING consecutive mathematical
;; integer indices beginning at INDEX. Thus CLS-MAP-OCC is the exact finite
;; cardinality of {i | LOWER <= i < UPPER and XS[i] = VALUE}.

(defun cls-map-occ-step
    (value xs index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if (equal value (cls-nth-int xs index))
         1
       0)
     (cls-map-occ-step
      value
      xs
      (+ index 1)
      (- remaining 1)))))

(defun cls-map-occ (value xs lower upper)
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (cls-map-occ-step
       value xs lower (- upper lower))
    0))

;; These predicates preserve the source universal quantifiers over all
;; mathematical integer indices.

(defun-sk cls-copy-segment-p
    (destination source offset)
  (forall (x)
    (implies
     (integerp x)
     (implies
      (and
       (<= offset x)
       (< x (len destination)))
      (equal
       (cls-nth-int destination x)
       (cls-nth-int source (- x offset)))))))

(defun-sk cls-prefix-equal-p
    (left right upper)
  (forall (x)
    (implies
     (integerp x)
     (implies
      (and
       (<= 0 x)
       (< x upper))
      (equal
       (cls-nth-int left x)
       (cls-nth-int right x))))))

(defun-sk cls-occurrences-match-p
    (array source offset)
  (forall (x)
    (implies
     (integerp x)
     (equal
      (cls-map-occ
       x array offset (len array))
      (cls-count-occ x source)))))

;; This is the source's extensional equality between lookup after List.set
;; and Function.update over every mathematical integer argument.

(defun-sk cls-set-function-equal-p
    (array index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (cls-nth-int
       (cls-list-set
        array
        (cls-int-to-nat index)
        value)
       argument)
      (if (equal argument index)
          value
        (cls-nth-int array argument))))))

;; A1 remains universally quantified over the full source list-of-integers
;; domain. Its hypotheses and three-part conclusion retain their nested
;; implication scope from the recursive-call verification condition.

(defun-sk cls-all-recursive-results-p
    (offset source original tail updated next-offset)
  (forall (a1)
    (implies
     (cls-integer-list-p a1)
     (implies
      (equal (len a1) (len updated))
      (implies
       (and
        (cls-copy-segment-p
         a1 tail next-offset)
        (cls-prefix-equal-p
         a1 updated next-offset)
        (cls-occurrences-match-p
         a1 tail next-offset))
       (and
        (cls-copy-segment-p
         a1 source offset)
        (cls-prefix-equal-p
         a1 original offset)
        (cls-occurrences-match-p
         a1 source offset)))))))

(defun cls-cons-branch-p (offset source array)
  (let* ((head (car source))
         (tail (cdr source))
         (updated
          (cls-list-set
           array
           (cls-int-to-nat offset)
           head))
         (next-offset (+ offset 1)))
    (and
     (<= 0 offset)
     (< offset (len array))
     (implies
      (equal (len updated) (len array))
      (implies
       (cls-set-function-equal-p
        array offset head)
       (and
        (and
         (equal (cdr source) tail)
         (<= 0 next-offset)
         (equal
          (len tail)
          (- (len updated) next-offset)))
        (cls-all-recursive-results-p
         offset
         source
         array
         tail
         updated
         next-offset)))))))

(defun
  ntp4vc-pearl-verifythis-2019-ghc-sort-top-copy-listqtvc-statement
  (offset source array)
  (implies
   (and
    (integerp offset)
    (cls-integer-list-p source)
    (cls-integer-list-p array)
    (<= 0 offset)
    (equal
     (len source)
     (- (len array) offset)))
   (if (endp source)
       (and
        (cls-copy-segment-p
         array source offset)
        (cls-occurrences-match-p
         array source offset))
     (cls-cons-branch-p
      offset source array))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
