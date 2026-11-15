;; Statement-only formalization of VERINA corpus artifact verina_basic_32,
;; catalog title "swapFirstAndLast": a deterministic nonempty integer-array
;; program swaps its first and last entries while preserving every interior
;; entry. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-32-int-array-p (array)
  (declare (xargs :measure (acl2-count array)))
  (if (consp array)
      (and
       (integerp (car array))
       (verina-basic-32-int-array-p (cdr array)))
    (equal array nil)))

;; This is Lean natural-number subtraction on the source Nat arguments.

(defun verina-basic-32-nat-sub (left right)
  (if (and
       (natp left)
       (natp right))
      (nfix (- left right))
    0))

;; The source precondition says exactly that the input array is nonempty. The
;; Array Int domain remains explicit in the final correctness proposition.

(defun verina-basic-32-swap-first-and-last-precond (a)
  (< 0 (len a)))

;; This is the exact ordered pair of source Array.set! operations on every
;; input satisfying the precondition. Both indices are then in bounds, so
;; ACL2 NTH and UPDATE-NTH coincide with the source reads and writes. The
;; proof-valued precondition argument is computationally irrelevant and erased.

(defun verina-basic-32-swap-first-and-last (a)
  (let* ((first (nth 0 a))
         (last-index
          (verina-basic-32-nat-sub (len a) 1))
         (last (nth last-index a)))
    (update-nth
     last-index
     first
     (update-nth 0 last a))))

;; Starting at index 1, this checks exactly COUNT consecutive entries. With
;; COUNT = result.size - 2, it is the source List.range(...).all condition for
;; every interior index and is vacuously true for arrays of size one or two.

(defun verina-basic-32-interior-unchanged-p
    (a result index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and
     (equal (nth index result)
            (nth index a))
     (verina-basic-32-interior-unchanged-p
      a
      result
      (+ 1 (nfix index))
      (- count 1)))))

;; This is the complete source postcondition: equal sizes, exchanged endpoint
;; values, and equality at every interior position.

(defun verina-basic-32-swap-first-and-last-postcond
    (a result)
  (and
   (verina-basic-32-int-array-p a)
   (verina-basic-32-int-array-p result)
   (equal (len result) (len a))
   (equal
    (nth 0 result)
    (nth
     (verina-basic-32-nat-sub (len a) 1)
     a))
   (equal
    (nth
     (verina-basic-32-nat-sub (len result) 1)
     result)
    (nth 0 a))
   (verina-basic-32-interior-unchanged-p
    a
    result
    1
    (verina-basic-32-nat-sub (len result) 2))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int domain, applies the source precondition, and
;; connects the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-32-swap-first-and-last-spec-satisfied-statement ()
  (forall (a)
    (implies
     (and
      (verina-basic-32-int-array-p a)
      (verina-basic-32-swap-first-and-last-precond a))
     (verina-basic-32-swap-first-and-last-postcond
      a
      (verina-basic-32-swap-first-and-last a)))))

(value-triple :itpeval-statement-checked)
:q
