;; Statement-only formalization of VERINA corpus artifact verina_basic_88,
;; catalog title "ToArray": converting an integer list to an array preserves
;; its length and every element at the same index. This file contains no proof.

(in-package "ACL2")

;; Finite Lean List Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-88-int-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-basic-88-int-list-p (cdr xs)))
    (equal xs nil)))

;; Finite Lean Array Int values have the same canonical sequence
;; representation, with a separate predicate retaining the result type.

(defun verina-basic-88-int-array-p (array)
  (declare (xargs :measure (acl2-count array)))
  (if (consp array)
      (and
       (integerp (car array))
       (verina-basic-88-int-array-p (cdr array)))
    (equal array nil)))

;; The source precondition is True. The List Int binder domain remains
;; explicit in the final correctness proposition.

(defun verina-basic-88-to-array-precond (xs)
  (declare (ignore xs))
  t)

;; Under the canonical finite-sequence representations above, List.toArray is
;; exactly the identity map: it changes the container type but preserves every
;; entry and the sequence length. The proof-valued precondition argument is
;; computationally irrelevant and is erased.

(defun verina-basic-88-to-array (xs)
  xs)

;; List.get! and Array.get! on integer containers both return the indexed
;; entry when present and the inhabited integer default zero otherwise.

(defun verina-basic-88-list-read (index xs)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp xs)
        (if (zp index)
            (car xs)
          (verina-basic-88-list-read
           (- index 1)
           (cdr xs)))
      0)))

(defun verina-basic-88-array-read (index array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp array)
        (if (zp index)
            (car array)
          (verina-basic-88-array-read
           (- index 1)
           (cdr array)))
      0)))

;; This predicate preserves the source postcondition's universal Nat
;; quantifier and its equality at every index valid for the input list.

(defun-sk verina-basic-88-every-index-preserved-p
    (xs result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len xs)))
     (equal
      (verina-basic-88-array-read i result)
      (verina-basic-88-list-read i xs)))))

;; This is the complete source postcondition, including the typed input and
;; result domains, equal size, and pointwise preservation. The unused
;; proof-valued precondition argument is erased.

(defun verina-basic-88-to-array-postcond
    (xs result)
  (and
   (verina-basic-88-int-list-p xs)
   (verina-basic-88-int-array-p result)
   (equal (len result) (len xs))
   (verina-basic-88-every-index-preserved-p
    xs
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer list, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact
;; executable list-to-array conversion.

(defun-sk
    verina-basic-88-to-array-spec-satisfied-statement
    ()
  (forall (xs)
    (implies
     (and
      (verina-basic-88-int-list-p xs)
      (verina-basic-88-to-array-precond xs))
     (verina-basic-88-to-array-postcond
      xs
      (verina-basic-88-to-array xs)))))

(value-triple :itpeval-statement-checked)
:q
