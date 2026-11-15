;; Statement-only formalization of VERINA corpus artifact verina_basic_97,
;; catalog title "TestArrayElements": a deterministic integer-array program
;; sets one valid indexed element to 60 while preserving the array size and
;; every other element. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-97-integer-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-97-integer-array-p
        (cdr a)))
    (equal a nil)))

;; This is exactly the source precondition. The Array Int and Nat binder
;; domains remain explicit in the final correctness proposition.

(defun verina-basic-97-test-array-elements-precond
    (a j)
  (< j (len a)))

;; Array.get! on Array Int returns the indexed entry when present and the
;; inhabited integer default zero when the natural index is out of bounds.

(defun verina-basic-97-array-read (index a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp a)
        (if (zp index)
            (car a)
          (verina-basic-97-array-read
           (- index 1)
           (cdr a)))
      0)))

;; Array.set! replaces an in-bounds entry and leaves the array unchanged when
;; its natural index is out of bounds.

(defun verina-basic-97-array-set
    (index value a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      a
    (if (consp a)
        (if (zp index)
            (cons value (cdr a))
          (cons
           (car a)
           (verina-basic-97-array-set
            (- index 1)
            value
            (cdr a))))
      nil)))

;; The proof-valued precondition argument has no computational effect and is
;; erased. This exact deterministic update preserves the complete source
;; implementation a.set! j 60.

(defun verina-basic-97-test-array-elements
    (a j)
  (verina-basic-97-array-set j 60 a))

;; This predicate preserves the source postcondition's universal Nat binder:
;; every valid array index distinct from J retains its original value.

(defun-sk
    verina-basic-97-all-other-elements-unchanged-p
    (a j result)
  (forall (k)
    (implies
     (and
      (natp k)
      (< k (len a))
      (not (equal k j)))
     (equal
      (verina-basic-97-array-read k result)
      (verina-basic-97-array-read k a)))))

;; This is the complete source postcondition: size preservation, value 60 at
;; J, and preservation of every other valid element. The proof-valued
;; precondition argument is unused and therefore erased.

(defun verina-basic-97-test-array-elements-postcond
    (a j result)
  (and
   (verina-basic-97-integer-array-p a)
   (natp j)
   (verina-basic-97-integer-array-p result)
   (equal (len result) (len a))
   (equal
    (verina-basic-97-array-read j result)
    60)
   (verina-basic-97-all-other-elements-unchanged-p
    a
    j
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array and natural index, assumes exactly the
;; source bounds precondition, and applies the complete postcondition to the
;; exact executable result.

(defun-sk
    verina-basic-97-test-array-elements-spec-satisfied-statement
    ()
  (forall (a j)
    (implies
     (and
      (verina-basic-97-integer-array-p a)
      (natp j)
      (verina-basic-97-test-array-elements-precond
       a
       j))
     (verina-basic-97-test-array-elements-postcond
      a
      j
      (verina-basic-97-test-array-elements
       a
       j)))))

(value-triple :itpeval-statement-checked)
:q
