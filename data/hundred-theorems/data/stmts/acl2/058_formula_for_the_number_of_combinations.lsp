;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__058, "Formula for the Number of Combinations":
;; for every finite set represented by a duplicate-free true list, the family
;; of its k-element subsets has cardinality choose(n,k), where n is the set's
;; cardinality. The family is enumerated by one order-preserving list for each
;; subset. This file contains no proof.

(in-package "ACL2")

(defun ht058-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (ht058-binomial-coefficient (- n 1) k)
       (ht058-binomial-coefficient (- n 1) (- k 1)))))

(defun ht058-prepend-to-each (value sets)
  (if (atom sets)
      nil
    (cons (cons value (car sets))
          (ht058-prepend-to-each value (cdr sets)))))

(defun ht058-subsets-of-size (k set-elements)
  (declare (xargs :measure (acl2-count set-elements)))
  (if (atom set-elements)
      (if (zp k)
          (list nil)
        nil)
    (if (zp k)
        (list nil)
      (append
       (ht058-subsets-of-size k (cdr set-elements))
       (ht058-prepend-to-each
        (car set-elements)
        (ht058-subsets-of-size (- k 1) (cdr set-elements)))))))

(defun hundred-theorems-058-formula-for-the-number-of-combinations-statement
    (n k set-elements)
  (implies
   (and (natp n)
        (natp k)
        (true-listp set-elements)
        (no-duplicatesp-equal set-elements)
        (equal (len set-elements) n))
   (equal
    (len (ht058-subsets-of-size k set-elements))
    (ht058-binomial-coefficient n k))))

(value-triple :itpeval-statement-checked)
:q
