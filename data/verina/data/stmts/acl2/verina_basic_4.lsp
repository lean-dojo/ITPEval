;; Statement-only formalization of VERINA corpus artifact verina_basic_4,
;; catalog title "kthElement": a deterministic integer-array program returns
;; the kth entry under a valid 1-based natural index, with its exact
;; membership-and-index postcondition. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-4-int-array-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (integerp (car arr))
       (verina-basic-4-int-array-p (cdr arr)))
    (equal arr nil)))

;; This is the source validity condition for the 1-based natural index.

(defun verina-basic-4-kth-element-precond (arr k)
  (and
   (natp k)
   (<= 1 k)
   (<= k (len arr))))

;; NFIX of an integer difference is Lean's truncated Nat subtraction.

(defun verina-basic-4-nat-sub (left right)
  (nfix (- left right)))

;; Array.get! on Array Int returns the in-bounds entry and the inhabited
;; integer default zero outside the array.

(defun verina-basic-4-nth-default-zero (index arr)
  (if (and
       (natp index)
       (< index (len arr)))
      (nth index arr)
    0))

;; The proof-valued precondition argument has no computational effect and is
;; erased. This is exactly the source lookup at the zero-based index k - 1.

(defun verina-basic-4-kth-element (arr k)
  (verina-basic-4-nth-default-zero
   (verina-basic-4-nat-sub k 1)
   arr))

;; This recursive Boolean scan is Array.any applied to
;; (fun x => x = result and x = arr[k - 1]!).

(defun verina-basic-4-any-result-and-selected-p
    (remaining result selected)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (and
           (equal (car remaining) result)
           (equal (car remaining) selected))
          t
        (verina-basic-4-any-result-and-selected-p
         (cdr remaining)
         result
         selected))
    nil))

(defun verina-basic-4-kth-element-postcond
    (arr k result)
  (and
   (verina-basic-4-int-array-p arr)
   (natp k)
   (integerp result)
   (verina-basic-4-any-result-and-selected-p
    arr
    result
    (verina-basic-4-nth-default-zero
     (verina-basic-4-nat-sub k 1)
     arr))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the full Array Int and Nat domains, applies the source precondition,
;; and connects the complete postcondition to the exact executable result.

(defun-sk verina-basic-4-kth-element-spec-satisfied-statement ()
  (forall (arr k)
    (implies
     (and
      (verina-basic-4-int-array-p arr)
      (natp k)
      (verina-basic-4-kth-element-precond arr k))
     (verina-basic-4-kth-element-postcond
      arr
      k
      (verina-basic-4-kth-element arr k)))))

(value-triple :itpeval-statement-checked)
:q
