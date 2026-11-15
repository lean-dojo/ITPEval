;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sumrange_CumulativeArray_updateqtvc: the cumulative-array point-update
;; verification condition, including loop-invariant preservation, restoration
;; of prefix sums, and the updated-array frame property. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite integer lists represent Why3 arrays of mathematical integers.
;; Total integer lookup returns the default value zero for every negative or
;; out-of-range index.

(defun sumrange-update-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (sumrange-update-integer-list-p (cdr xs)))))

(defun sumrange-update-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun sumrange-update-nth-int (index xs)
  (if (and
       (integerp index)
       (<= 0 index))
      (let ((value (nth index xs)))
        (if (integerp value)
            value
          0))
    0))

;; Source List.set leaves a list unchanged when its natural index is outside
;; the list.

(defun sumrange-update-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (sumrange-update-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; On every source-valid interval this reverse recursion denotes exactly
;; ArraySum.sum, summing the entries with LOWER <= index < UPPER.

(defun sumrange-update-range-sum (xs lower upper)
  (declare
   (xargs :measure
          (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (sumrange-update-nth-int (- upper 1) xs)
     (sumrange-update-range-sum
      xs lower (- upper 1)))))

;; The source cumulative-array invariant, retaining its universal quantifier
;; over all mathematical integer indices.

(defun-sk sumrange-update-cumulative-entries-p (c a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len c)))
      (equal
       (sumrange-update-nth-int index c)
       (sumrange-update-range-sum a 0 index))))))

(defun sumrange-update-is-cumulative-array-for-p (c a)
  (and
   (sumrange-update-integer-list-p c)
   (sumrange-update-integer-list-p a)
   (equal (len c) (+ (len a) 1))
   (sumrange-update-cumulative-entries-p c a)))

;; Equality between the integer-indexed lookup after List.set and the source
;; Function.update is represented extensionally over every integer argument.

(defun-sk sumrange-update-set-function-equal-p
    (xs index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (sumrange-update-nth-int
       argument
       (sumrange-update-list-set
        xs
        (sumrange-update-int-to-nat index)
        value))
      (if (equal argument index)
          value
        (sumrange-update-nth-int argument xs))))))

;; The two loop invariants: entries at or after LOWER still differ by INCR,
;; while entries before UPPER are already the new prefix sums.

(defun-sk sumrange-update-suffix-adjusted-p
    (c updated-a lower incr)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (<= lower k)
       (< k (len c)))
      (equal
       (sumrange-update-nth-int k c)
       (-
        (sumrange-update-range-sum updated-a 0 k)
        incr))))))

(defun-sk sumrange-update-prefix-correct-p
    (c updated-a upper)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (<= 0 k)
       (< k upper))
      (equal
       (sumrange-update-nth-int k c)
       (sumrange-update-range-sum updated-a 0 k))))))

;; The source postcondition also records the updated cell and pointwise frame
;; property for every other valid integer index.

(defun-sk sumrange-update-other-cells-unchanged-p
    (updated-a old-a index)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (and
        (<= 0 k)
        (< k (len updated-a)))
       (not (equal k index)))
      (equal
       (sumrange-update-nth-int k updated-a)
       (sumrange-update-nth-int k old-a))))))

(defun sumrange-update-postcondition-p
    (c updated-a old-a index value)
  (and
   (sumrange-update-is-cumulative-array-for-p
    c updated-a)
   (equal
    (sumrange-update-nth-int index updated-a)
    value)
   (sumrange-update-other-cells-unchanged-p
    updated-a old-a index)))

;; One universally quantified loop iteration, including the repeated bounds
;; and both update antecedents from the generated verification condition.

(defun sumrange-update-loop-step-p
    (c1 updated-a j incr)
  (and
   (<= 0 j)
   (< j (len c1))
   (let* ((o4
           (+
            (sumrange-update-nth-int j c1)
            incr))
          (updated-c
           (sumrange-update-list-set
            c1
            (sumrange-update-int-to-nat j)
            o4)))
     (and
      (<= 0 j)
      (< j (len c1))
      (implies
       (equal (len updated-c) (len c1))
       (implies
        (sumrange-update-set-function-equal-p
         c1 j o4)
        (and
         (sumrange-update-suffix-adjusted-p
          updated-c updated-a (+ j 1) incr)
         (sumrange-update-prefix-correct-p
          updated-c updated-a (+ j 1)))))))))

(defun sumrange-update-loop-premise-p
    (c1 updated-a j o2 o3 incr)
  (and
   (and
    (<= o3 j)
    (<= j o2))
   (sumrange-update-suffix-adjusted-p
    c1 updated-a j incr)
   (sumrange-update-prefix-correct-p
    c1 updated-a j)))

(defun-sk sumrange-update-all-loop-indices-p
    (c1 updated-a o2 o3 incr)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (sumrange-update-loop-premise-p
       c1 updated-a j o2 o3 incr)
      (sumrange-update-loop-step-p
       c1 updated-a j incr)))))

;; The loop-exit implication for one same-length intermediate cumulative
;; array.

(defun sumrange-update-loop-exit-p
    (c1 updated-a old-a index value o2 incr)
  (implies
   (and
    (sumrange-update-suffix-adjusted-p
     c1 updated-a (+ o2 1) incr)
    (sumrange-update-prefix-correct-p
     c1 updated-a (+ o2 1)))
   (sumrange-update-postcondition-p
    c1 updated-a old-a index value)))

(defun sumrange-update-intermediate-array-obligations-p
    (c1 updated-a old-a index value o2 o3 incr)
  (and
   (sumrange-update-all-loop-indices-p
    c1 updated-a o2 o3 incr)
   (sumrange-update-loop-exit-p
    c1 updated-a old-a index value o2 incr)))

(defun-sk sumrange-update-all-intermediate-arrays-p
    (c updated-a old-a index value o2 o3 incr)
  (forall (c1)
    (implies
     (sumrange-update-integer-list-p c1)
     (implies
      (equal (len c1) (len c))
      (sumrange-update-intermediate-array-obligations-p
       c1 updated-a old-a index value o2 o3 incr)))))

;; Preserve both generated branches for the loop range, including the
;; vacuous-range implication.

(defun sumrange-update-loop-continuation-p
    (c updated-a old-a index value incr)
  (let* ((o2 (- (len c) 1))
         (o3 (+ index 1)))
    (and
     (implies
      (<= o3 (+ o2 1))
      (and
       (and
        (sumrange-update-suffix-adjusted-p
         c updated-a o3 incr)
        (sumrange-update-prefix-correct-p
         c updated-a o3))
       (sumrange-update-all-intermediate-arrays-p
        c updated-a old-a index value o2 o3 incr)))
     (implies
      (< (+ o2 1) o3)
      (sumrange-update-postcondition-p
       c updated-a old-a index value)))))

;; The arguments encode the source theorem's universally quantified typed
;; parameters. The antecedent is exactly the cumulative-array and index
;; assumptions; the conclusion retains every bound, update antecedent,
;; quantified loop obligation, and final frame clause.

(defun
  ntp4vc-pearl-sumrange-cumulativearray-updateqtvc-statement
  (c a i v)
  (implies
   (and
    (sumrange-update-integer-list-p c)
    (sumrange-update-integer-list-p a)
    (integerp i)
    (integerp v)
    (sumrange-update-is-cumulative-array-for-p c a)
    (<= 0 i)
    (< i (len a)))
   (and
    (<= 0 i)
    (< i (len c))
    (let* ((o1 (+ i 1))
           (incr
            (+
             (- v (sumrange-update-nth-int o1 c))
             (sumrange-update-nth-int i c)))
           (updated-a
            (sumrange-update-list-set
             a
             (sumrange-update-int-to-nat i)
             v)))
      (and
       (and
        (<= 0 o1)
        (< o1 (len c)))
       (and
        (<= 0 i)
        (< i (len a))
        (implies
         (equal (len updated-a) (len a))
         (implies
          (sumrange-update-set-function-equal-p
           a i v)
          (sumrange-update-loop-continuation-p
           c updated-a a i v incr)))))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
