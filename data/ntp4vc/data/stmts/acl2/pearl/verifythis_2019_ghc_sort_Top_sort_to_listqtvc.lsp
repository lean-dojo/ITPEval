;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2019_ghc_sort_Top_sort_to_listqtvc: the verification
;; condition connecting monotonic cutpoints, sorted segment lists, and a
;; nondecreasing permutation with the input multiplicities and length.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite ACL2 integer lists represent Why3 lists and integer arrays
;; without bounding their lengths or element values. A list_seq record is
;; represented by its list field; its seq field is definitionally the reverse
;; of that list, exactly as required by the source type invariant.

(defun stl-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (stl-integer-list-p (cdr xs)))
    (equal xs nil)))

(defun stl-integer-list-list-p (xss)
  (declare (xargs :measure (acl2-count xss)))
  (if (consp xss)
      (and
       (stl-integer-list-p (car xss))
       (stl-integer-list-list-p (cdr xss)))
    (equal xss nil)))

;; Int.toNat maps negative integers to zero. Out-of-range source list reads
;; use the inhabited integer default zero in all three prover exports.

(defun stl-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun stl-nth-zero-nat (index xs)
  (declare (xargs :measure (nfix index)))
  (if (and
       (natp index)
       (consp xs))
      (if (zp index)
          (car xs)
        (stl-nth-zero-nat
         (- index 1)
         (cdr xs)))
    0))

(defun stl-nth-zero (xs index)
  (stl-nth-zero-nat
   (stl-int-to-nat index)
   xs))

(defun stl-cut-seq (cut-list)
  (reverse cut-list))

(defun stl-cut-read (cut-list index)
  (stl-nth-zero
   (stl-cut-seq cut-list)
   index))

(defun stl-cut-last (cut-list)
  (stl-cut-read
   cut-list
   (- (len (stl-cut-seq cut-list)) 1)))

;; These recursive predicates are the source nondecreasing-list relation,
;; right-folded concatenation, occurrence count, and finite-list permutation.

(defun stl-nondecreasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (<= (car xs) (cadr xs))
       (stl-nondecreasing-p (cdr xs)))
    t))

(defun stl-all-lists-nondecreasing-p (xss)
  (declare (xargs :measure (acl2-count xss)))
  (if (endp xss)
      t
    (and
     (stl-nondecreasing-p (car xss))
     (stl-all-lists-nondecreasing-p
      (cdr xss)))))

(defun stl-flatten (xss)
  (declare (xargs :measure (acl2-count xss)))
  (if (endp xss)
      nil
    (append
     (car xss)
     (stl-flatten (cdr xss)))))

(defun stl-count-occ (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      0
    (+
     (if (equal value (car xs)) 1 0)
     (stl-count-occ value (cdr xs)))))

(defun stl-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (stl-remove-first
        value
        (cdr xs))))))

(defun stl-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (stl-permutation-p
      (cdr left)
      (stl-remove-first
       (car left)
       right)))))

;; MAP-OCC counts the source array values at every mathematical integer index
;; in the half-open interval [LOWER, UPPER).

(defun stl-map-occ-step
    (value array index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if (equal
          value
          (stl-nth-zero array index))
         1
       0)
     (stl-map-occ-step
      value
      array
      (+ index 1)
      (- remaining 1)))))

(defun stl-map-occ
    (value array lower upper)
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (stl-map-occ-step
       value array lower (- upper lower))
    0))

;; The monotonic-segment disjunction preserves both universal integer
;; quantifiers and the strict/nonincreasing alternatives from the source.

(defun-sk stl-strict-segment-p
    (array lower upper)
  (forall (z1 z2)
    (implies
     (and
      (integerp z1)
      (integerp z2))
     (implies
      (and
       (<= lower z1)
       (< z1 z2)
       (< z2 upper))
      (< (stl-nth-zero array z1)
         (stl-nth-zero array z2))))))

(defun-sk stl-nonincreasing-segment-p
    (array lower upper)
  (forall (z1 z2)
    (implies
     (and
      (integerp z1)
      (integerp z2))
     (implies
      (and
       (<= lower z1)
       (< z1 z2)
       (< z2 upper))
      (<= (stl-nth-zero array z2)
          (stl-nth-zero array z1))))))

(defun stl-monotonic-segment-p
    (array lower upper)
  (or
   (stl-strict-segment-p
    array lower upper)
   (stl-nonincreasing-segment-p
    array lower upper)))

(defun-sk stl-all-segments-monotonic-p
    (array cut-list)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (<= 0 k)
       (< k (- (len (stl-cut-seq cut-list)) 1)))
      (let ((ck
             (stl-cut-read cut-list k))
            (ck1
             (stl-cut-read cut-list (+ k 1))))
        (stl-monotonic-segment-p
         array ck ck1))))))

(defun-sk stl-cut-seq-nondecreasing-p
    (cut-list)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j))
     (implies
      (and
       (<= 0 i)
       (< i j)
       (< j (len (stl-cut-seq cut-list))))
      (<= (stl-cut-read cut-list i)
          (stl-cut-read cut-list j))))))

(defun stl-cut-list-bounded-p
    (cut-list upper)
  (declare (xargs :measure (acl2-count cut-list)))
  (if (endp cut-list)
      t
    (and
     (<= 0 (car cut-list))
     (<= (car cut-list) upper)
     (stl-cut-list-bounded-p
      (cdr cut-list)
      upper))))

(defun stl-cutpoints-postconditions-p
    (array cut-list)
  (and
   (equal (stl-cut-read cut-list 0) 0)
   (equal (stl-cut-last cut-list)
          (len array))
   (<= 2 (len cut-list))
   (stl-cut-list-bounded-p
    cut-list
    (len array))
   (stl-all-segments-monotonic-p
    array cut-list)
   (stl-cut-seq-nondecreasing-p
    cut-list)))

;; These predicates retain the internal universal quantifiers over integer
;; values, lists of sorted segments, and arbitrary merge results.

(defun-sk stl-flatten-counts-match-interval-p
    (array cut-list segment-lists)
  (forall (x)
    (implies
     (integerp x)
     (equal
      (stl-count-occ
       x
       (stl-flatten segment-lists))
      (stl-map-occ
       x
       array
       (stl-cut-read cut-list 0)
       (stl-cut-last cut-list))))))

(defun-sk stl-result-counts-match-array-p
    (array result)
  (forall (x)
    (implies
     (integerp x)
     (equal
      (stl-map-occ
       x array 0 (len array))
      (stl-count-occ x result)))))

(defun-sk stl-all-merge-results-p
    (array segment-lists)
  (forall (result)
    (implies
     (stl-integer-list-p result)
     (implies
      (and
       (stl-nondecreasing-p result)
       (stl-permutation-p
        result
        (stl-flatten segment-lists)))
      (and
       (stl-nondecreasing-p result)
       (stl-result-counts-match-array-p
        array result)
       (equal
        (len result)
        (len array)))))))

(defun-sk stl-all-segment-list-results-p
    (array cut-list)
  (forall (segment-lists)
    (implies
     (stl-integer-list-list-p segment-lists)
     (implies
      (and
       (stl-all-lists-nondecreasing-p
        segment-lists)
       (stl-flatten-counts-match-interval-p
        array cut-list segment-lists))
      (and
       (stl-all-lists-nondecreasing-p
        segment-lists)
       (stl-all-merge-results-p
        array segment-lists))))))

(defun stl-cutpoint-result-obligation-p
    (array cut-list)
  (and
   (< 0 (len cut-list))
   (stl-cut-seq-nondecreasing-p
    cut-list)
   (stl-cut-list-bounded-p
    cut-list
    (len array))
   (stl-all-segments-monotonic-p
    array cut-list)
   (stl-all-segment-list-results-p
    array cut-list)))

(defun-sk stl-all-cutpoint-results-p
    (array)
  (forall (cut-list)
    (implies
     (stl-integer-list-p cut-list)
     (implies
      (stl-cutpoints-postconditions-p
       array cut-list)
      (stl-cutpoint-result-obligation-p
       array cut-list)))))

;; This closed predicate is the complete unproved sort_to_list verification
;; condition, including its nonempty-array assumption and repeated first
;; conjunct.

(defun-sk
    ntp4vc-pearl-verifythis-2019-ghc-sort-top-sort-to-listqtvc-statement
    ()
  (forall (array)
    (implies
     (stl-integer-list-p array)
     (implies
      (< 0 (len array))
      (and
       (< 0 (len array))
       (stl-all-cutpoint-results-p
        array))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
