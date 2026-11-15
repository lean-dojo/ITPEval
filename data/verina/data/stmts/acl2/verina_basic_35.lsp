;; Statement-only formalization of VERINA corpus artifact verina_basic_35,
;; catalog title "MoveZeroesToEnd": a deterministic stable partition moves
;; every zero in an integer array after all nonzero entries while preserving
;; the complete permutation, prefix, and suffix contract. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-35-int-array-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (integerp (car arr))
       (verina-basic-35-int-array-p (cdr arr)))
    (equal arr nil)))

;; The source precondition is True. The Array Int binder domain remains
;; explicit in the final correctness proposition.

(defun verina-basic-35-move-zeroes-to-end-precond (arr)
  (declare (ignore arr))
  t)

;; These two stable filters are exactly the source List.filter calls.

(defun verina-basic-35-filter-nonzero (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (if (not (equal (car arr) 0))
          (cons
           (car arr)
           (verina-basic-35-filter-nonzero (cdr arr)))
        (verina-basic-35-filter-nonzero (cdr arr)))
    nil))

(defun verina-basic-35-filter-zero (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (if (equal (car arr) 0)
          (cons
           (car arr)
           (verina-basic-35-filter-zero (cdr arr)))
        (verina-basic-35-filter-zero (cdr arr)))
    nil))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. APPEND followed by the list-to-array representation is
;; exactly Array.mk (nonZeros ++ zeros).

(defun verina-basic-35-move-zeroes-to-end (arr)
  (append
   (verina-basic-35-filter-nonzero arr)
   (verina-basic-35-filter-zero arr)))

;; This is List.idxOf 0: it returns the first zero index, or the list length
;; when zero is absent.

(defun verina-basic-35-first-zero-index (values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (if (equal (car values) 0)
          0
        (+ 1
           (verina-basic-35-first-zero-index
            (cdr values))))
    0))

;; Exact total representations of List.take and List.drop on natural counts.

(defun verina-basic-35-take (count values)
  (declare (xargs :measure (nfix count)))
  (if (and
       (natp count)
       (< 0 count)
       (consp values))
      (cons
       (car values)
       (verina-basic-35-take
        (- count 1)
        (cdr values)))
    nil))

(defun verina-basic-35-drop (count values)
  (declare (xargs :measure (nfix count)))
  (if (and
       (natp count)
       (< 0 count)
       (consp values))
      (verina-basic-35-drop
       (- count 1)
       (cdr values))
    values))

;; Removing the first equal entry and recurring gives an exact Boolean
;; characterization of List.isPerm, including duplicate multiplicities.

(defun verina-basic-35-member-p (value values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (or
       (equal value (car values))
       (verina-basic-35-member-p
        value
        (cdr values)))
    nil))

(defun verina-basic-35-remove-first (value values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (if (equal value (car values))
          (cdr values)
        (cons
         (car values)
         (verina-basic-35-remove-first
          value
          (cdr values))))
    nil))

(defun verina-basic-35-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (verina-basic-35-member-p (car left) right)
       (verina-basic-35-permutation-p
        (cdr left)
        (verina-basic-35-remove-first
         (car left)
         right)))
    (equal right nil)))

;; This is the complete source postcondition. The proof-valued True
;; precondition argument is unused and therefore erased.

(defun verina-basic-35-move-zeroes-to-end-postcond
    (arr result)
  (let ((first-zero-index
         (verina-basic-35-first-zero-index result)))
    (and
     (verina-basic-35-int-array-p arr)
     (verina-basic-35-int-array-p result)
     (verina-basic-35-permutation-p result arr)
     (equal
      (verina-basic-35-take first-zero-index result)
      (verina-basic-35-filter-nonzero arr))
     (equal
      (verina-basic-35-drop first-zero-index result)
      (verina-basic-35-filter-zero arr)))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int domain, applies the source True precondition,
;; and connects the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-35-move-zeroes-to-end-spec-satisfied-statement
    ()
  (forall (arr)
    (implies
     (and
      (verina-basic-35-int-array-p arr)
      (verina-basic-35-move-zeroes-to-end-precond arr))
     (verina-basic-35-move-zeroes-to-end-postcond
      arr
      (verina-basic-35-move-zeroes-to-end arr)))))

(value-triple :itpeval-statement-checked)
:q
