;; Statement-only formalization of VERINA corpus artifact verina_basic_94,
;; catalog title "iter_copy": a deterministic integer-array loop copies every
;; input element in order into a newly constructed array. This file contains
;; no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-94-int-array-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (integerp (car s))
       (verina-basic-94-int-array-p (cdr s)))
    (equal s nil)))

;; The source precondition is True. The Array Int binder domain remains
;; explicit in the final correctness proposition.

(defun verina-basic-94-iter-copy-precond (s)
  (declare (ignore s))
  t)

;; REMAINING is exactly the unprocessed suffix beginning at the source loop
;; index. Appending its first element to ACC is Lean Array.push, and consuming
;; the suffix is equivalent to incrementing the index while it is below the
;; source array size. The source get? none branch is unreachable on this typed
;; suffix.

(defun verina-basic-94-iter-copy-loop
    (remaining acc)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-basic-94-iter-copy-loop
       (cdr remaining)
       (append acc (list (car remaining))))
    acc))

;; The proof-valued True precondition argument has no computational effect and
;; is erased. The loop starts at index zero with an empty accumulator.

(defun verina-basic-94-iter-copy (s)
  (verina-basic-94-iter-copy-loop s nil))

;; Array.get! on Array Int returns the indexed element when present and the
;; inhabited integer default zero outside the array.

(defun verina-basic-94-array-read (index s)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp s)
        (if (zp index)
            (car s)
          (verina-basic-94-array-read
           (- index 1)
           (cdr s)))
      0)))

;; This predicate is the source postcondition's universal Nat quantifier over
;; every valid input-array index.

(defun-sk verina-basic-94-elements-identical-p
    (s result)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index (len s)))
     (equal
      (verina-basic-94-array-read index s)
      (verina-basic-94-array-read index result)))))

;; This is the complete source postcondition: equal array sizes and equal
;; elements at every valid input index. The proof-valued precondition argument
;; is unused and therefore erased.

(defun verina-basic-94-iter-copy-postcond
    (s result)
  (and
   (verina-basic-94-int-array-p s)
   (verina-basic-94-int-array-p result)
   (equal (len s) (len result))
   (verina-basic-94-elements-identical-p s result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact executable
;; copy result.

(defun-sk
    verina-basic-94-iter-copy-spec-satisfied-statement
    ()
  (forall (s)
    (implies
     (and
      (verina-basic-94-int-array-p s)
      (verina-basic-94-iter-copy-precond s))
     (verina-basic-94-iter-copy-postcond
      s
      (verina-basic-94-iter-copy s)))))

(value-triple :itpeval-statement-checked)
:q
