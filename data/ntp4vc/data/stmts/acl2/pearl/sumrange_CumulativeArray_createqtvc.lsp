;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sumrange_CumulativeArray_createqtvc: the verification condition for
;; creating an integer cumulative-sum array, including zero initialization,
;; loop-invariant preservation, and the final range-sum specification. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite integer lists represent Why3 arrays of mathematical integers.
;; Int.toNat sends negative indices to zero, and the exported total list lookup
;; returns the integer default zero outside the list.

(defun sumrange-create-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (sumrange-create-integer-list-p (cdr xs)))))

(defun sumrange-create-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun sumrange-create-nth-int (index xs)
  (let ((value
         (nth
          (sumrange-create-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; Why3's array update, like List.set in the official exports, leaves the list
;; unchanged when its natural-number index is out of bounds.

(defun sumrange-create-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (sumrange-create-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; This reverse recursion is definitionally equivalent on every valid source
;; interval to ArraySum.sum: it sums exactly the entries with
;; LOWER <= index < UPPER.

(defun sumrange-create-range-sum (xs lower upper)
  (declare
   (xargs :measure
          (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (sumrange-create-nth-int (- upper 1) xs)
     (sumrange-create-range-sum
      xs lower (- upper 1)))))

;; The cumulative-array predicate from the source theory.

(defun-sk sumrange-create-cumulative-entries-p (c a)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i (len c)))
      (equal
       (sumrange-create-nth-int i c)
       (sumrange-create-range-sum a 0 i))))))

(defun sumrange-create-is-cumulative-array-for-p (c a)
  (and
   (sumrange-create-integer-list-p c)
   (sumrange-create-integer-list-p a)
   (equal (len c) (+ (len a) 1))
   (sumrange-create-cumulative-entries-p c a)))

;; Pointwise clauses over all mathematical integer indices.

(defun-sk sumrange-create-zero-initialized-p (s upper)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i upper))
      (equal
       (sumrange-create-nth-int i s)
       0)))))

(defun-sk sumrange-create-prefix-sums-p (s a upper)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (<= 0 k)
       (< k upper))
      (equal
       (sumrange-create-nth-int k s)
       (sumrange-create-range-sum a 0 k))))))

;; Equality of the two integer-indexed functions in the source update
;; antecedent, with Function.update represented by the conditional at INDEX.

(defun-sk sumrange-create-set-function-equal-p
    (xs index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (sumrange-create-nth-int
       argument
       (sumrange-create-list-set
        xs
        (sumrange-create-int-to-nat index)
        value))
      (if (equal argument index)
          value
        (sumrange-create-nth-int argument xs))))))

;; The body of one universally quantified loop iteration.  O2 and O3 are kept
;; separately to mirror the two source let-bindings.

(defun sumrange-create-loop-step-p (s1 a i)
  (let* ((o2 (- i 1))
         (o3 (- i 1))
         (o4
          (+
           (sumrange-create-nth-int o3 s1)
           (sumrange-create-nth-int o2 a)))
         (updated
          (sumrange-create-list-set
           s1
           (sumrange-create-int-to-nat i)
           o4)))
    (and
     (and
      (<= 0 o2)
      (< o2 (len a)))
     (and
      (and
       (<= 0 o3)
       (< o3 (len s1)))
      (and
       (and
        (<= 0 i)
        (< i (len s1)))
       (implies
        (equal (len updated) (len s1))
        (implies
         (sumrange-create-set-function-equal-p
          s1 i o4)
         (sumrange-create-prefix-sums-p
          updated a (+ i 1)))))))))

(defun-sk sumrange-create-all-loop-indices-p (s1 a l)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (and
        (<= 1 i)
        (<= i l))
       (sumrange-create-prefix-sums-p s1 a i))
      (sumrange-create-loop-step-p s1 a i)))))

;; Preserve the universal quantifier over every same-length intermediate array.

(defun-sk sumrange-create-all-intermediate-arrays-p (s a l)
  (forall (s1)
    (implies
     (sumrange-create-integer-list-p s1)
     (implies
      (equal (len s1) (len s))
      (and
       (sumrange-create-all-loop-indices-p s1 a l)
       (implies
        (sumrange-create-prefix-sums-p
         s1 a (+ l 1))
        (sumrange-create-is-cumulative-array-for-p
         s1 a)))))))

;; This is the conclusion for one zero-initialized result array S.  Both loop
;; range branches remain explicit exactly as in the generated VC.

(defun sumrange-create-initial-array-conclusion-p (s a l)
  (and
   (implies
    (<= 1 (+ l 1))
    (and
     (sumrange-create-prefix-sums-p s a 1)
     (sumrange-create-all-intermediate-arrays-p
      s a l)))
   (implies
    (< (+ l 1) 1)
    (sumrange-create-is-cumulative-array-for-p
     s a))))

(defun-sk sumrange-create-all-initial-arrays-p (a l o1)
  (forall (s)
    (implies
     (sumrange-create-integer-list-p s)
     (implies
      (and
       (sumrange-create-zero-initialized-p s o1)
       (equal (len s) o1))
      (sumrange-create-initial-array-conclusion-p
       s a l)))))

(defun
  ntp4vc-pearl-sumrange-cumulativearray-createqtvc-statement
  (a)
  (implies
   (sumrange-create-integer-list-p a)
   (let* ((l (len a))
          (o1 (+ l 1)))
     (and
      (<= 0 o1)
      (sumrange-create-all-initial-arrays-p
       a l o1)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
