;; Statement-only formalization of VERINA corpus artifact verina_basic_77,
;; catalog title "modify_array_element": a deterministic two-dimensional
;; natural-array program updates one selected inner entry while preserving
;; all other entries and both array sizes. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Nat values are represented bijectively by proper ACL2
;; lists whose entries range over all natural numbers.

(defun verina-basic-77-nat-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (natp (car a))
       (verina-basic-77-nat-array-p (cdr a)))
    (equal a nil)))

;; A Lean Array (Array Nat) is represented by a proper list of the represented
;; natural arrays, preserving arbitrary finite outer and inner sizes.

(defun verina-basic-77-nat-array-array-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (verina-basic-77-nat-array-p (car arr))
       (verina-basic-77-nat-array-array-p (cdr arr)))
    (equal arr nil)))

;; Array.get! on Array (Array Nat) returns the indexed inner array when present
;; and the inhabited default empty array otherwise.

(defun verina-basic-77-outer-read (arr index)
  (if (and
       (natp index)
       (< index (len arr)))
      (nth index arr)
    nil))

;; Array.get! on Array Nat returns the indexed natural when present and the
;; inhabited natural default zero otherwise.

(defun verina-basic-77-inner-read (a index)
  (if (and
       (natp index)
       (< index (len a)))
      (nth index a)
    0))

;; This total update agrees with Array.set!: it replaces an in-bounds entry
;; and leaves the represented array unchanged for an out-of-bounds Nat index.

(defun verina-basic-77-array-set (a index value)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      a
    (if (consp a)
        (if (zp index)
            (cons value (cdr a))
          (cons
           (car a)
           (verina-basic-77-array-set
            (cdr a)
            (- index 1)
            value)))
      nil)))

;; This is the complete source precondition. The Array (Array Nat) and Nat
;; binder domains remain explicit in the final correctness proposition.

(defun verina-basic-77-modify-array-element-precond
    (arr index1 index2 val)
  (declare (ignore val))
  (and
   (< index1 (len arr))
   (< index2
      (len
       (verina-basic-77-outer-read arr index1)))))

;; This helper exactly preserves updateInner a idx val = a.set! idx val.

(defun verina-basic-77-update-inner (a index val)
  (verina-basic-77-array-set a index val))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. The two LET bindings and ordered updates preserve the complete
;; source implementation.

(defun verina-basic-77-modify-array-element
    (arr index1 index2 val)
  (let* ((inner
          (verina-basic-77-outer-read arr index1))
         (inner-prime
          (verina-basic-77-update-inner
           inner
           index2
           val)))
    (verina-basic-77-array-set
     arr
     index1
     inner-prime)))

;; This is the source postcondition's universal Nat binder for outer indices:
;; every in-bounds inner array except the selected one is unchanged.

(defun-sk verina-basic-77-other-inner-arrays-unchanged-p
    (arr index1 result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len arr))
      (not (equal i index1)))
     (equal
      (verina-basic-77-outer-read result i)
      (verina-basic-77-outer-read arr i)))))

;; This is the source postcondition's universal Nat binder for inner indices:
;; every in-bounds entry except the selected one is unchanged.

(defun-sk verina-basic-77-other-elements-unchanged-p
    (arr index1 index2 result)
  (forall (j)
    (implies
     (and
      (natp j)
      (< j
         (len
          (verina-basic-77-outer-read arr index1)))
      (not (equal j index2)))
     (equal
      (verina-basic-77-inner-read
       (verina-basic-77-outer-read result index1)
       j)
      (verina-basic-77-inner-read
       (verina-basic-77-outer-read arr index1)
       j)))))

;; This is the complete source postcondition. The unused proof-valued
;; precondition argument is erased, while its typed array binders are made
;; explicit by the two representation predicates.

(defun verina-basic-77-modify-array-element-postcond
    (arr index1 index2 val result)
  (and
   (verina-basic-77-nat-array-array-p arr)
   (verina-basic-77-nat-array-array-p result)
   (equal (len result) (len arr))
   (equal
    (len
     (verina-basic-77-outer-read result index1))
    (len
     (verina-basic-77-outer-read arr index1)))
   (verina-basic-77-other-inner-arrays-unchanged-p
    arr
    index1
    result)
   (verina-basic-77-other-elements-unchanged-p
    arr
    index1
    index2
    result)
   (equal
    (verina-basic-77-inner-read
     (verina-basic-77-outer-read result index1)
     index2)
    val)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite Array (Array Nat) and all natural parameters, assumes
;; exactly the source bounds precondition, and applies the full postcondition
;; to the exact executable result.

(defun-sk
    verina-basic-77-modify-array-element-spec-satisfied-statement
    ()
  (forall (arr index1 index2 val)
    (implies
     (and
      (verina-basic-77-nat-array-array-p arr)
      (natp index1)
      (natp index2)
      (natp val)
      (verina-basic-77-modify-array-element-precond
       arr
       index1
       index2
       val))
     (verina-basic-77-modify-array-element-postcond
      arr
      index1
      index2
      val
      (verina-basic-77-modify-array-element
       arr
       index1
       index2
       val)))))

(value-triple :itpeval-statement-checked)
:q
