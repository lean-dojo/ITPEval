;; Statement-only formalization of VERINA corpus artifact verina_basic_20,
;; catalog title "uniqueProduct": a deterministic integer-array program
;; multiplies each distinct input value exactly once and equates its result
;; with the product of List.eraseDups. This file contains no proof.

(in-package "ACL2")

;; ACL2 proper lists of integers represent exactly the finite Array Int inputs.

(defun verina-basic-20-int-array-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (integerp (car arr))
       (verina-basic-20-int-array-p (cdr arr)))
    (equal arr nil)))

;; The source precondition is True. The Array Int domain remains explicit in
;; the final correctness proposition.

(defun verina-basic-20-unique-product-precond (arr)
  (declare (ignore arr))
  t)

;; REMAINING is the unprocessed array suffix. SEEN represents exactly the
;; HashSet membership state; its list order is unobservable. PRODUCT is the
;; source loop accumulator. Traversing the suffix is equivalent to increasing
;; the source index from zero through the array size.

(defun verina-basic-20-unique-product-loop
    (remaining seen product)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((x (car remaining)))
        (if (member-equal x seen)
            (verina-basic-20-unique-product-loop
             (cdr remaining)
             seen
             product)
          (verina-basic-20-unique-product-loop
           (cdr remaining)
           (cons x seen)
           (* product x))))
    product))

;; The proof-valued True precondition argument is computationally irrelevant.
;; Empty input therefore starts and ends with product one, exactly as in Lean.

(defun verina-basic-20-unique-product (arr)
  (verina-basic-20-unique-product-loop arr nil 1))

;; Lean's List.eraseDups keeps the first occurrence of each integer. The
;; accumulator stores those occurrences in reverse order until the final
;; reverse restores their input order.

(defun verina-basic-20-erase-dups-loop
    (remaining seen-reversed)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (member-equal (car remaining) seen-reversed)
          (verina-basic-20-erase-dups-loop
           (cdr remaining)
           seen-reversed)
        (verina-basic-20-erase-dups-loop
         (cdr remaining)
         (cons (car remaining) seen-reversed)))
    (reverse seen-reversed)))

(defun verina-basic-20-erase-dups (arr)
  (verina-basic-20-erase-dups-loop arr nil))

;; This is List.foldl multiplication with initial accumulator one.

(defun verina-basic-20-foldl-product (xs accumulator)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (verina-basic-20-foldl-product
       (cdr xs)
       (* accumulator (car xs)))
    accumulator))

(defun verina-basic-20-unique-product-postcond
    (arr result)
  (and
   (verina-basic-20-int-array-p arr)
   (integerp result)
   (let ((expected
          (verina-basic-20-foldl-product
           (verina-basic-20-erase-dups arr)
           1)))
     (and
      (equal (- result expected) 0)
      (equal (- expected result) 0)))))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Array Int input and True precondition, and applies the full
;; two-sided postcondition to the exact executable result.

(defun-sk
    verina-basic-20-unique-product-spec-satisfied-statement
    ()
  (forall (arr)
    (implies
     (and
      (verina-basic-20-int-array-p arr)
      (verina-basic-20-unique-product-precond arr))
     (verina-basic-20-unique-product-postcond
      arr
      (verina-basic-20-unique-product arr)))))

(value-triple :itpeval-statement-checked)
:q
