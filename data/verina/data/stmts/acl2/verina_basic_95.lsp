;; Statement-only formalization of VERINA corpus artifact verina_basic_95,
;; catalog title "swap": a deterministic integer-array program exchanges the
;; entries at two valid indices and leaves every other entry unchanged. This
;; file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-95-int-array-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (integerp (car arr))
       (verina-basic-95-int-array-p (cdr arr)))
    (equal arr nil)))

;; On the typed Int domain, NFIX is exactly Lean Int.toNat: it returns the
;; nonnegative integer unchanged and returns zero for a negative integer.

(defun verina-basic-95-int-to-nat (x)
  (nfix x))

;; Array.get! on Array Int returns the indexed entry when present and the
;; inhabited integer default zero when the natural index is out of bounds.

(defun verina-basic-95-array-read (index arr)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp arr)
        (if (zp index)
            (car arr)
          (verina-basic-95-array-read
           (- index 1)
           (cdr arr)))
      0)))

;; Array.set! replaces an in-bounds entry and leaves the array unchanged when
;; its natural index is out of bounds.

(defun verina-basic-95-array-set (index value arr)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      arr
    (if (consp arr)
        (if (zp index)
            (cons value (cdr arr))
          (cons
           (car arr)
           (verina-basic-95-array-set
            (- index 1)
            value
            (cdr arr))))
      nil)))

;; This is exactly the source precondition: both integer indices are
;; nonnegative and their Int.toNat values are within the input array.

(defun verina-basic-95-swap-precond (arr i j)
  (and
   (<= 0 i)
   (<= 0 j)
   (< (verina-basic-95-int-to-nat i)
      (len arr))
   (< (verina-basic-95-int-to-nat j)
      (len arr))))

;; The proof-valued precondition argument has no computational effect and is
;; erased. These local bindings preserve the source's ordered computation:
;; first write the old J entry at I, then write the old I entry at J.

(defun verina-basic-95-swap (arr i j)
  (let* ((i-nat
          (verina-basic-95-int-to-nat i))
         (j-nat
          (verina-basic-95-int-to-nat j))
         (arr1
          (verina-basic-95-array-set
           i-nat
           (verina-basic-95-array-read j-nat arr)
           arr))
         (arr2
          (verina-basic-95-array-set
           j-nat
           (verina-basic-95-array-read i-nat arr)
           arr1)))
    arr2))

;; This predicate is the source postcondition's universal Nat quantifier:
;; every valid index distinct from I and J has its original value.

(defun-sk verina-basic-95-all-other-entries-unchanged-p
    (arr i j result)
  (forall (k)
    (implies
     (and
      (natp k)
      (< k (len arr))
      (not
       (equal
        k
        (verina-basic-95-int-to-nat i)))
      (not
       (equal
        k
        (verina-basic-95-int-to-nat j))))
     (equal
      (verina-basic-95-array-read k result)
      (verina-basic-95-array-read k arr)))))

;; This is the complete source postcondition: size preservation, the two
;; exchanged entries, and preservation of every other entry. The proof-valued
;; precondition argument is unused and therefore erased.

(defun verina-basic-95-swap-postcond
    (arr i j result)
  (and
   (verina-basic-95-int-array-p arr)
   (integerp i)
   (integerp j)
   (verina-basic-95-int-array-p result)
   (equal (len result) (len arr))
   (equal
    (verina-basic-95-array-read
     (verina-basic-95-int-to-nat i)
     result)
    (verina-basic-95-array-read
     (verina-basic-95-int-to-nat j)
     arr))
   (equal
    (verina-basic-95-array-read
     (verina-basic-95-int-to-nat j)
     result)
    (verina-basic-95-array-read
     (verina-basic-95-int-to-nat i)
     arr))
   (verina-basic-95-all-other-entries-unchanged-p
    arr
    i
    j
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array and both arbitrary integer indices, assumes
;; exactly the source precondition, and applies the complete postcondition to
;; the exact executable result.

(defun-sk
    verina-basic-95-swap-spec-satisfied-statement
    ()
  (forall (arr i j)
    (implies
     (and
      (verina-basic-95-int-array-p arr)
      (integerp i)
      (integerp j)
      (verina-basic-95-swap-precond arr i j))
     (verina-basic-95-swap-postcond
      arr
      i
      j
      (verina-basic-95-swap arr i j)))))

(value-triple :itpeval-statement-checked)
:q
