;; Statement-only formalization of VERINA corpus artifact verina_basic_68,
;; catalog title "LinearSearch": a deterministic left-to-right scan of an
;; integer array returns the first target index, or the array size when the
;; target is absent. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-68-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-68-int-array-p (cdr a)))
    (equal a nil)))

;; The source precondition is True. The Array Int and Int binder domains
;; remain explicit in the final correctness proposition.

(defun verina-basic-68-linear-search-precond (a e)
  (declare (ignore a e))
  t)

;; REMAINING is the suffix beginning at the source loop index INDEX. The
;; equality branch returns INDEX immediately; otherwise the scan advances by
;; one. Exhausting the suffix returns its index, which is the original array
;; size.

(defun verina-basic-68-linear-search-loop
    (remaining e index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (equal (car remaining) e)
          index
        (verina-basic-68-linear-search-loop
         (cdr remaining)
         e
         (+ index 1)))
    index))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. Starting the exact loop at natural index zero reproduces the
;; executable Lean implementation.

(defun verina-basic-68-linear-search (a e)
  (verina-basic-68-linear-search-loop a e 0))

;; Array.get! on Array Int returns the in-bounds entry and the inhabited
;; integer default zero outside the array.

(defun verina-basic-68-nth-default-zero (index a)
  (if (and
       (natp index)
       (< index (len a)))
      (nth index a)
    0))

;; This predicate preserves the source postcondition's universal Nat binder
;; and states that every index strictly before RESULT contains a value
;; different from E.

(defun-sk verina-basic-68-no-target-before-p
    (a e result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i result))
     (not
      (equal
       (verina-basic-68-nth-default-zero i a)
       e)))))

;; This is the complete source postcondition, including the result bound, the
;; size-or-match disjunction, and the absence of an earlier match.

(defun verina-basic-68-linear-search-postcond
    (a e result)
  (and
   (verina-basic-68-int-array-p a)
   (integerp e)
   (natp result)
   (<= result (len a))
   (or
    (equal result (len a))
    (equal
     (verina-basic-68-nth-default-zero result a)
     e))
   (verina-basic-68-no-target-before-p
    a
    e
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int and Int domains, assumes exactly the source
;; True precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-68-linear-search-spec-satisfied-statement
    ()
  (forall (a e)
    (implies
     (and
      (verina-basic-68-int-array-p a)
      (integerp e)
      (verina-basic-68-linear-search-precond a e))
     (verina-basic-68-linear-search-postcond
      a
      e
      (verina-basic-68-linear-search a e)))))

(value-triple :itpeval-statement-checked)
:q
