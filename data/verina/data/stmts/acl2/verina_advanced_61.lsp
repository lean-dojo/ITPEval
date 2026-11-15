;; Statement-only formalization of VERINA corpus artifact verina_advanced_61,
;; "productExceptSelf": a deterministic prefix-and-suffix product program
;; returns, at each integer-list index, the product of every other element.
;; This file contains no proof.

(in-package "ACL2")

;; Lean's List Int domain is represented by proper ACL2 lists of integers.

(defun verina-advanced-61-integer-listp (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (integerp (car nums))
       (verina-advanced-61-integer-listp (cdr nums)))
    (equal nums nil)))

(defun verina-advanced-61-product-except-self-precond (nums)
  (declare (ignore nums))
  t)

;; List.getLast! on List Int returns zero on the empty list. The source folds
;; start from [1], so every operational use below is on a nonempty list.

(defun verina-advanced-61-get-last-default-zero (values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (if (consp (cdr values))
          (verina-advanced-61-get-last-default-zero
           (cdr values))
        (car values))
    0))

;; This is the source foldl step acc ++ [acc.getLast! * x], retaining the
;; append-based accumulator semantics and traversal order.

(defun verina-advanced-61-prefix-fold (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-61-prefix-fold
       (cdr remaining)
       (append
        accumulator
        (list
         (*
          (verina-advanced-61-get-last-default-zero
           accumulator)
          (car remaining)))))
    accumulator))

(defun verina-advanced-61-computepref (nums)
  (verina-advanced-61-prefix-fold nums (list 1)))

;; The suffix helper reverses the input, performs the identical fold from
;; [1], and reverses the complete accumulated list, exactly as in the source.

(defun verina-advanced-61-compute-suffix (nums)
  (reverse
   (verina-advanced-61-prefix-fold
    (reverse nums)
    (list 1))))

;; List.get! on List Int returns zero when the index is out of bounds.

(defun verina-advanced-61-nth-default-zero (index values)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp values)
        (if (zp index)
            (car values)
          (verina-advanced-61-nth-default-zero
           (- index 1)
           (cdr values)))
      0)))

;; INDEX and REMAINING enumerate List.range n in increasing order and map the
;; source expression pref[i]! * suffix[i+1]! over that range.

(defun verina-advanced-61-build-result
    (index remaining pref suffix)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (*
      (verina-advanced-61-nth-default-zero
       index
       pref)
      (verina-advanced-61-nth-default-zero
       (+ index 1)
       suffix))
     (verina-advanced-61-build-result
      (+ index 1)
      (- remaining 1)
      pref
      suffix))))

;; The proof-valued True precondition argument is computationally irrelevant.
;; The empty branch and both helper computations remain explicit.

(defun verina-advanced-61-product-except-self (nums)
  (let ((n (len nums)))
    (if (equal n 0)
        nil
      (let ((pref
             (verina-advanced-61-computepref nums))
            (suffix
             (verina-advanced-61-compute-suffix nums)))
        (verina-advanced-61-build-result
         0
         n
         pref
         suffix)))))

;; This is the source-local List.myprod definition.

(defun verina-advanced-61-myprod (values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (*
       (car values)
       (verina-advanced-61-myprod (cdr values)))
    1))

(defun verina-advanced-61-take (count values)
  (declare (xargs :measure (nfix count)))
  (if (not (natp count))
      nil
    (if (zp count)
        nil
      (if (consp values)
          (cons
           (car values)
           (verina-advanced-61-take
            (- count 1)
            (cdr values)))
        nil))))

(defun verina-advanced-61-drop (count values)
  (declare (xargs :measure (nfix count)))
  (if (not (natp count))
      nil
    (if (zp count)
        values
      (if (consp values)
          (verina-advanced-61-drop
           (- count 1)
           (cdr values))
        nil))))

;; Option Int is represented by :none or the tagged pair (:some . value).

(defun verina-advanced-61-nth-option (index values)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      :none
    (if (consp values)
        (if (zp index)
            (cons :some (car values))
          (verina-advanced-61-nth-option
           (- index 1)
           (cdr values)))
      :none)))

;; This finite recursion is List.range nums.length followed by List.all. The
;; tagged equality preserves the source comparison with `some` at each index.

(defun verina-advanced-61-all-products-correct-p
    (index remaining nums result)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (equal
      (verina-advanced-61-nth-option index result)
      (cons
       :some
       (*
        (verina-advanced-61-myprod
         (verina-advanced-61-take index nums))
        (verina-advanced-61-myprod
         (verina-advanced-61-drop
          (+ index 1)
          nums)))))
     (verina-advanced-61-all-products-correct-p
      (+ index 1)
      (- remaining 1)
      nums
      result))))

(defun verina-advanced-61-product-except-self-postcond
    (nums result)
  (and
   (verina-advanced-61-integer-listp nums)
   (verina-advanced-61-integer-listp result)
   (equal (len nums) (len result))
   (verina-advanced-61-all-products-correct-p
    0
    (len nums)
    nums
    result)))

;; This predicate is the unproved final correctness proposition connecting
;; the complete postcondition to the exact executable result.

(defun
    verina-advanced-61-product-except-self-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-61-integer-listp nums)
    (verina-advanced-61-product-except-self-precond nums))
   (verina-advanced-61-product-except-self-postcond
    nums
    (verina-advanced-61-product-except-self nums))))

(value-triple :itpeval-statement-checked)
:q
