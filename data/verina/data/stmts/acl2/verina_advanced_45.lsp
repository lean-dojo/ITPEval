;; Statement-only formalization of VERINA corpus artifact verina_advanced_45,
;; "maxSubarraySum": the deterministic Kadane-style integer-list program
;; computes a sum that occurs among the nonempty contiguous subarrays and is
;; at least every such sum, returning zero on an empty list. This file contains
;; no proof.

(in-package "ACL2")

(defun verina-advanced-45-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-45-integer-listp
        (cdr xs)))
    (equal xs nil)))

;; The source precondition is True. The List Int binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-45-max-subarray-sum-precond (xs)
  (declare (ignore xs))
  t)

(defun verina-advanced-45-int-max (left right)
  (if (< left right)
      right
    left))

;; This is the source local helper. For each element, NEW-CURRENT is the larger
;; of starting a new subarray and extending the current one, and NEW-GLOBAL is
;; the larger of the previous global maximum and NEW-CURRENT.

(defun verina-advanced-45-max-subarray-sum-helper
    (lst current-maximum global-maximum)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (let* ((x (car lst))
             (new-current
              (verina-advanced-45-int-max
               x
               (+ current-maximum x)))
             (new-global
              (verina-advanced-45-int-max
               global-maximum
               new-current)))
        (verina-advanced-45-max-subarray-sum-helper
         (cdr lst)
         new-current
         new-global))
    global-maximum))

;; The proof-valued True precondition argument has no computational effect.
;; This preserves the empty-list branch and initializes both helper
;; accumulators from the first element exactly as in the source program.

(defun verina-advanced-45-max-subarray-sum (xs)
  (if (consp xs)
      (verina-advanced-45-max-subarray-sum-helper
       (cdr xs)
       (car xs)
       (car xs))
    0))

(defun verina-advanced-45-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      xs
    (if (consp xs)
        (verina-advanced-45-drop
         (- count 1)
         (cdr xs))
      nil)))

(defun verina-advanced-45-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp xs)
        (cons
         (car xs)
         (verina-advanced-45-take
          (- count 1)
          (cdr xs)))
      nil)))

(defun verina-advanced-45-list-sum (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (+
       (car xs)
       (verina-advanced-45-list-sum
        (cdr xs)))
    0))

;; At a fixed START, LENGTH and REMAINING-LENGTHS reproduce
;; List.range' 1 (xs.length - start), hence lengths
;; 1,...,xs.length-start in increasing order.

(defun verina-advanced-45-subarray-sums-at-start
    (xs start length remaining-lengths)
  (declare (xargs :measure (nfix remaining-lengths)))
  (if (zp remaining-lengths)
      nil
    (cons
     (verina-advanced-45-list-sum
      (verina-advanced-45-take
       length
       (verina-advanced-45-drop
        start
        xs)))
     (verina-advanced-45-subarray-sums-at-start
      xs
      start
      (+ length 1)
      (- remaining-lengths 1)))))

;; START and REMAINING-STARTS reproduce List.range (xs.length + 1).
;; APPEND implements flatMap, so this is exactly the postcondition's ordered
;; list of sums of all nonempty contiguous subarrays.

(defun verina-advanced-45-all-subarray-sums-from
    (xs start remaining-starts total-length)
  (declare (xargs :measure (nfix remaining-starts)))
  (if (zp remaining-starts)
      nil
    (append
     (verina-advanced-45-subarray-sums-at-start
      xs
      start
      1
      (nfix (- total-length start)))
     (verina-advanced-45-all-subarray-sums-from
      xs
      (+ start 1)
      (- remaining-starts 1)
      total-length))))

(defun verina-advanced-45-all-subarray-sums (xs)
  (let ((total-length (len xs)))
    (verina-advanced-45-all-subarray-sums-from
     xs
     0
     (+ total-length 1)
     total-length)))

;; These recursions are respectively List.any equality and List.all (· <=
;; result) over the exact subarray-sum list.

(defun verina-advanced-45-has-result-subarray-p
    (subarray-sums result)
  (declare (xargs :measure (acl2-count subarray-sums)))
  (if (consp subarray-sums)
      (or
       (equal (car subarray-sums) result)
       (verina-advanced-45-has-result-subarray-p
        (cdr subarray-sums)
        result))
    nil))

(defun verina-advanced-45-all-subarray-sums-at-most-p
    (subarray-sums result)
  (declare (xargs :measure (acl2-count subarray-sums)))
  (if (consp subarray-sums)
      (and
       (<= (car subarray-sums) result)
       (verina-advanced-45-all-subarray-sums-at-most-p
        (cdr subarray-sums)
        result))
    t))

(defun verina-advanced-45-max-subarray-sum-postcond
    (xs result)
  (let* ((subarray-sums
          (verina-advanced-45-all-subarray-sums xs))
         (has-result-subarray
          (verina-advanced-45-has-result-subarray-p
           subarray-sums
           result))
         (is-maximum
          (verina-advanced-45-all-subarray-sums-at-most-p
           subarray-sums
           result)))
    (and
     (verina-advanced-45-integer-listp xs)
     (integerp result)
     (if (equal xs nil)
         (equal result 0)
       (and
        has-result-subarray
        is-maximum)))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and True precondition; its
;; conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-45-max-subarray-sum-spec-satisfied-statement
    (xs)
  (implies
   (and
    (verina-advanced-45-integer-listp xs)
    (verina-advanced-45-max-subarray-sum-precond xs))
   (verina-advanced-45-max-subarray-sum-postcond
    xs
    (verina-advanced-45-max-subarray-sum xs))))

(value-triple :itpeval-statement-checked)
:q
