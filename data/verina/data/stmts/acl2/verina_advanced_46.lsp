;; Statement-only formalization of VERINA corpus artifact verina_advanced_46,
;; "maxSubarraySum": the deterministic integer-list program computes the
;; maximum sum among all contiguous subarrays, including the empty subarray,
;; and returns zero when every input integer is negative. This file contains
;; no proof.

(in-package "ACL2")

(defun verina-advanced-46-integer-listp (numbers)
  (declare (xargs :measure (acl2-count numbers)))
  (if (consp numbers)
      (and
       (integerp (car numbers))
       (verina-advanced-46-integer-listp
        (cdr numbers)))
    (equal numbers nil)))

;; The source precondition is True. The List Int binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-46-max-subarray-sum-precond
    (numbers)
  (declare (ignore numbers))
  t)

(defun verina-advanced-46-int-max (left right)
  (if (< left right)
      right
    left))

;; Exact translation of the source local isAllNegative recursion. Its empty
;; case is true, and any nonnegative element makes the result false.

(defun verina-advanced-46-is-all-negative (numbers)
  (declare (xargs :measure (acl2-count numbers)))
  (if (consp numbers)
      (if (>= (car numbers) 0)
          nil
        (verina-advanced-46-is-all-negative
         (cdr numbers)))
    t))

;; Exact translation of findMaxProduct. For a list with at least two elements,
;; the recursion processes the second element and continues from that same
;; element, just as the source recurses on y :: rest.

(defun verina-advanced-46-find-max-product
    (numbers current-maximum current-sum)
  (declare (xargs :measure (acl2-count numbers)))
  (if (consp numbers)
      (if (consp (cdr numbers))
          (let* ((next (car (cdr numbers)))
                 (new-sum
                  (verina-advanced-46-int-max
                   next
                   (+ current-sum next)))
                 (new-maximum
                  (verina-advanced-46-int-max
                   current-maximum
                   new-sum)))
            (verina-advanced-46-find-max-product
             (cdr numbers)
             new-maximum
             new-sum))
        (verina-advanced-46-int-max
         current-maximum
         (car numbers)))
    current-maximum))

;; This preserves handleList as a separate executable helper. NFIX is exactly
;; Int.toNat on the integer result: it is the identity for nonnegative
;; integers and zero for negative integers.

(defun verina-advanced-46-handle-list (numbers)
  (if (consp numbers)
      (if (verina-advanced-46-is-all-negative numbers)
          0
        (let* ((initial-maximum
                (verina-advanced-46-int-max
                 0
                 (car numbers)))
               (start-sum
                (verina-advanced-46-int-max
                 0
                 (car numbers)))
               (result
                (verina-advanced-46-find-max-product
                 numbers
                 initial-maximum
                 start-sum)))
          (nfix result)))
    0))

;; The proof-valued True precondition argument has no computational effect.
;; ACL2 naturals are integers, so the source coercion of handleList's Nat
;; result back to Int is represented by the identity.

(defun verina-advanced-46-max-subarray-sum (numbers)
  (verina-advanced-46-handle-list numbers))

(defun verina-advanced-46-drop (count numbers)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      numbers
    (if (consp numbers)
        (verina-advanced-46-drop
         (- count 1)
         (cdr numbers))
      nil)))

(defun verina-advanced-46-take (count numbers)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp numbers)
        (cons
         (car numbers)
         (verina-advanced-46-take
          (- count 1)
          (cdr numbers)))
      nil)))

(defun verina-advanced-46-list-sum (numbers)
  (declare (xargs :measure (acl2-count numbers)))
  (if (consp numbers)
      (+
       (car numbers)
       (verina-advanced-46-list-sum
        (cdr numbers)))
    0))

;; At a fixed START, the initial LENGTH zero and REMAINING-LENGTHS equal to
;; numbers.length - start + 1 reproduce the inner List.range exactly. Thus
;; every start contributes its empty subarray before its positive lengths.

(defun verina-advanced-46-subarray-sums-at-start
    (numbers start length remaining-lengths)
  (declare (xargs :measure (nfix remaining-lengths)))
  (if (zp remaining-lengths)
      nil
    (cons
     (verina-advanced-46-list-sum
      (verina-advanced-46-take
       length
       (verina-advanced-46-drop
        start
        numbers)))
     (verina-advanced-46-subarray-sums-at-start
      numbers
      start
      (+ length 1)
      (- remaining-lengths 1)))))

;; START and REMAINING-STARTS reproduce List.range (numbers.length + 1).
;; APPEND implements flatMap, preserving the source's ordered list of all
;; contiguous-subarray sums, including every generated empty sum.

(defun verina-advanced-46-all-subarray-sums-from
    (numbers start remaining-starts total-length)
  (declare (xargs :measure (nfix remaining-starts)))
  (if (zp remaining-starts)
      nil
    (append
     (verina-advanced-46-subarray-sums-at-start
      numbers
      start
      0
      (+ (nfix (- total-length start)) 1))
     (verina-advanced-46-all-subarray-sums-from
      numbers
      (+ start 1)
      (- remaining-starts 1)
      total-length))))

(defun verina-advanced-46-all-subarray-sums (numbers)
  (let ((total-length (len numbers)))
    (verina-advanced-46-all-subarray-sums-from
     numbers
     0
     (+ total-length 1)
     total-length)))

;; These recursions are respectively List.contains result and
;; List.all (fun sum => sum <= result) over the exact flatMap result.

(defun verina-advanced-46-contains-result-p
    (subarray-sums result)
  (declare (xargs :measure (acl2-count subarray-sums)))
  (if (consp subarray-sums)
      (or
       (equal (car subarray-sums) result)
       (verina-advanced-46-contains-result-p
        (cdr subarray-sums)
        result))
    nil))

(defun verina-advanced-46-all-sums-at-most-p
    (subarray-sums result)
  (declare (xargs :measure (acl2-count subarray-sums)))
  (if (consp subarray-sums)
      (and
       (<= (car subarray-sums) result)
       (verina-advanced-46-all-sums-at-most-p
        (cdr subarray-sums)
        result))
    t))

(defun verina-advanced-46-max-subarray-sum-postcond
    (numbers result)
  (let ((subarray-sums
         (verina-advanced-46-all-subarray-sums
          numbers)))
    (and
     (verina-advanced-46-integer-listp numbers)
     (integerp result)
     (verina-advanced-46-contains-result-p
      subarray-sums
      result)
     (verina-advanced-46-all-sums-at-most-p
      subarray-sums
      result))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and True precondition; its
;; conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-46-max-subarray-sum-spec-satisfied-statement
    (numbers)
  (implies
   (and
    (verina-advanced-46-integer-listp numbers)
    (verina-advanced-46-max-subarray-sum-precond
     numbers))
   (verina-advanced-46-max-subarray-sum-postcond
    numbers
    (verina-advanced-46-max-subarray-sum numbers))))

(value-triple :itpeval-statement-checked)
:q
