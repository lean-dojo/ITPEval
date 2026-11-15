;; Statement-only formalization of VERINA corpus artifact verina_advanced_43,
;; "maxStrength": the deterministic bitmask program computes the maximum
;; product of a nonempty subset of an integer list, with its exhaustive
;; subsequence-product correctness contract. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-43-integer-listp (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (integerp (car nums))
       (verina-advanced-43-integer-listp (cdr nums)))
    (equal nums nil)))

(defun verina-advanced-43-max-strength-precond (nums)
  (not (equal nums nil)))

;; Traversing NUMS from left to right while dividing MASK by two reproduces
;; the source foldr over List.range: the current low bit is exactly the bit at
;; the current list index, and selected elements retain their original order.

(defun verina-advanced-43-subset-for-mask (nums mask)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (if (equal (mod mask 2) 1)
          (cons
           (car nums)
           (verina-advanced-43-subset-for-mask
            (cdr nums)
            (floor mask 2)))
        (verina-advanced-43-subset-for-mask
         (cdr nums)
         (floor mask 2)))
    nil))

;; REMAINING is the length of List.range (2 ^ nums.length). Starting MASK at
;; zero therefore enumerates precisely the source masks in increasing order.

(defun verina-advanced-43-enumerate-masked-subsets
    (nums mask remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (verina-advanced-43-subset-for-mask nums mask)
     (verina-advanced-43-enumerate-masked-subsets
      nums
      (+ mask 1)
      (- remaining 1)))))

(defun verina-advanced-43-power-set (nums)
  (verina-advanced-43-enumerate-masked-subsets
   nums
   0
   (expt 2 (len nums))))

(defun verina-advanced-43-filter-nonempty
    (subsets)
  (declare (xargs :measure (acl2-count subsets)))
  (if (consp subsets)
      (if (consp (car subsets))
          (cons
           (car subsets)
           (verina-advanced-43-filter-nonempty
            (cdr subsets)))
        (verina-advanced-43-filter-nonempty
         (cdr subsets)))
    nil))

;; This accumulator recursion is List.foldl multiplication with initial value
;; one, including the empty-list result.

(defun verina-advanced-43-product-foldl
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-43-product-foldl
       (cdr remaining)
       (* accumulator (car remaining)))
    accumulator))

(defun verina-advanced-43-map-products
    (subsets)
  (declare (xargs :measure (acl2-count subsets)))
  (if (consp subsets)
      (cons
       (verina-advanced-43-product-foldl
        (car subsets)
        1)
       (verina-advanced-43-map-products
        (cdr subsets)))
    nil))

(defun verina-advanced-43-max-tail
    (remaining current)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-43-max-tail
       (cdr remaining)
       (if (> (car remaining) current)
           (car remaining)
         current))
    current))

;; This is List.max? followed by Option.getD (-1000000).

(defun verina-advanced-43-max-get-default
    (values default)
  (if (consp values)
      (verina-advanced-43-max-tail
       (cdr values)
       (car values))
    default))

;; The proof-valued nonempty precondition argument is computationally
;; irrelevant. Every remaining definition is the exact executable content of
;; the source maxStrength body.

(defun verina-advanced-43-max-strength (nums)
  (let* ((subsets
          (verina-advanced-43-power-set nums))
         (nonempty
          (verina-advanced-43-filter-nonempty
           subsets))
         (products
          (verina-advanced-43-map-products
           nonempty)))
    (verina-advanced-43-max-get-default
     products
     -1000000)))

;; This direct recursion reproduces List.sublists: first all sublists of the
;; tail, then the same sublists with the current head prepended.

(defun verina-advanced-43-prepend-to-each
    (value sublists)
  (declare (xargs :measure (acl2-count sublists)))
  (if (consp sublists)
      (cons
       (cons value (car sublists))
       (verina-advanced-43-prepend-to-each
        value
        (cdr sublists)))
    nil))

(defun verina-advanced-43-sublists (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (let ((tail-sublists
             (verina-advanced-43-sublists
              (cdr nums))))
        (append
         tail-sublists
         (verina-advanced-43-prepend-to-each
          (car nums)
          tail-sublists)))
    (list nil)))

(defun verina-advanced-43-contains-value-p
    (values result)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (or
       (equal (car values) result)
       (verina-advanced-43-contains-value-p
        (cdr values)
        result))
    nil))

(defun verina-advanced-43-all-at-most-p
    (values result)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (and
       (<= (car values) result)
       (verina-advanced-43-all-at-most-p
        (cdr values)
        result))
    t))

(defun verina-advanced-43-max-strength-postcond
    (nums result)
  (let* ((sublists
          (verina-advanced-43-filter-nonempty
           (verina-advanced-43-sublists nums)))
         (products
          (verina-advanced-43-map-products
           sublists)))
    (and
     (verina-advanced-43-integer-listp nums)
     (integerp result)
     (verina-advanced-43-contains-value-p
      products
      result)
     (verina-advanced-43-all-at-most-p
      products
      result))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and nonempty-list precondition;
;; its conclusion applies the complete postcondition to the exact executable
;; result.

(defun verina-advanced-43-max-strength-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-43-integer-listp nums)
    (verina-advanced-43-max-strength-precond nums))
   (verina-advanced-43-max-strength-postcond
    nums
    (verina-advanced-43-max-strength nums))))

(value-triple :itpeval-statement-checked)
:q
