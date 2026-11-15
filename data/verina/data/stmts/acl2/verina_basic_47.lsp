;; Statement-only formalization of VERINA corpus artifact verina_basic_47,
;; catalog title "arraySum": a deterministic program sums every integer in a
;; nonempty array and satisfies the source sumTo contract. This file contains
;; no proof.

(in-package "ACL2")

;; A Lean Array Int is represented exactly by its finite sequence of entries:
;; a proper ACL2 list whose elements range over all integers.

(defun verina-basic-47-integer-array-p (array)
  (declare (xargs :measure (acl2-count array)))
  (if (consp array)
      (and
       (integerp (car array))
       (verina-basic-47-integer-array-p
        (cdr array)))
    (equal array nil)))

;; Lean Nat comparison a.size > 0 is exactly nonzero ACL2 list length.

(defun verina-basic-47-array-sum-precond (a)
  (> (len a) 0))

;; Under the sequence representation, Array.toList is the identity. This
;; recursion is exactly the integer List.sum used by the executable source
;; program, including zero as the sum of the empty list.

(defun verina-basic-47-array-sum (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (+ (car a)
         (verina-basic-47-array-sum
          (cdr a)))
    0))

;; Array.get! returns the in-bounds entry and the inhabited integer default
;; zero outside the represented array.

(defun verina-basic-47-nth-default-zero
    (index array)
  (if (and
       (natp index)
       (< index (len array)))
      (nth index array)
    0))

;; This is the source sumTo helper on its Nat argument: zero maps to zero, and
;; each successor adds the defaulting array entry at the preceding index.

(defun verina-basic-47-sum-to (a n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+
     (verina-basic-47-sum-to
      a
      (- n 1))
     (verina-basic-47-nth-default-zero
      (- n 1)
      a))))

;; The proof-valued precondition argument is computationally irrelevant and
;; does not occur in the source postcondition body. This preserves both its
;; subtraction equality and its greater-than-or-equal conjunct.

(defun verina-basic-47-array-sum-postcond
    (a result)
  (let ((expected
         (verina-basic-47-sum-to
          a
          (len a))))
    (and
     (verina-basic-47-integer-array-p a)
     (integerp result)
     (equal (- result expected) 0)
     (>= result expected))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array, assumes exactly the source nonempty-array
;; precondition, and connects the full postcondition to the exact executable
;; result.

(defun-sk
    verina-basic-47-array-sum-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-47-integer-array-p a)
      (verina-basic-47-array-sum-precond a))
     (verina-basic-47-array-sum-postcond
      a
      (verina-basic-47-array-sum a)))))

(value-triple :itpeval-statement-checked)
:q
