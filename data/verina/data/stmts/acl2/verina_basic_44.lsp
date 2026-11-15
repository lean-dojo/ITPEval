;; Statement-only formalization of VERINA corpus artifact verina_basic_44,
;; catalog title "isOddAtIndexOdd": a deterministic Boolean scan of an integer
;; array returns true exactly when every odd index contains an odd integer.
;; This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-44-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-44-int-array-p (cdr a)))
    (equal a nil)))

;; With positive divisor two, ACL2 MOD and Lean Int.emod agree on every
;; integer, so this is exactly the source isOdd helper.

(defun verina-basic-44-is-odd (n)
  (equal (mod n 2) 1))

;; The source precondition is True. The Array Int binder domain remains
;; explicit in the final correctness statement.

(defun verina-basic-44-is-odd-at-index-odd-precond (a)
  (declare (ignore a))
  t)

;; REMAINING is the suffix beginning at INDEX. This recursion fuses the
;; source mapIdx with the following Array.all: at each entry it tests exactly
;; !(isOdd index) || isOdd value, stopping at the first false result.

(defun verina-basic-44-is-odd-at-index-odd-aux
    (remaining index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (or
        (not (verina-basic-44-is-odd index))
        (verina-basic-44-is-odd (car remaining)))
       (verina-basic-44-is-odd-at-index-odd-aux
        (cdr remaining)
        (+ index 1)))
    t))

;; The proof-valued True precondition argument has no computational effect and
;; is erased. Starting at index zero gives the exact executable Boolean result.

(defun verina-basic-44-is-odd-at-index-odd (a)
  (verina-basic-44-is-odd-at-index-odd-aux a 0))

(defun verina-basic-44-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; This predicate preserves the source postcondition's universal Nat binder,
;; in-bounds hypothesis, and implication from odd index to odd array value.

(defun-sk verina-basic-44-all-odd-indices-have-odd-values-p
    (a)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len a))
      (verina-basic-44-is-odd i))
     (verina-basic-44-is-odd (nth i a)))))

;; ACL2 t and nil are the two Boolean values. Equality with the quantified
;; predicate is therefore exactly the source result ↔ condition postcondition.

(defun verina-basic-44-is-odd-at-index-odd-postcond
    (a result)
  (and
   (verina-basic-44-int-array-p a)
   (verina-basic-44-bool-p result)
   (equal
    result
    (verina-basic-44-all-odd-indices-have-odd-values-p a))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array, applies the True precondition, and connects
;; the complete postcondition to the exact executable implementation.

(defun-sk
    verina-basic-44-is-odd-at-index-odd-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-44-int-array-p a)
      (verina-basic-44-is-odd-at-index-odd-precond a))
     (verina-basic-44-is-odd-at-index-odd-postcond
      a
      (verina-basic-44-is-odd-at-index-odd a)))))

(value-triple :itpeval-statement-checked)
:q
