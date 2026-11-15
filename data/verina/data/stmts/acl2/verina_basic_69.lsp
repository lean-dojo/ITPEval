;; Statement-only formalization of VERINA corpus artifact verina_basic_69,
;; catalog title "LinearSearch": under the assumption that an integer array
;; contains a target, a deterministic left-to-right scan returns its first
;; occurrence index. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-69-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-69-int-array-p (cdr a)))
    (equal a nil)))

;; Array.get! on Array Int returns the in-bounds entry and the inhabited
;; integer default zero outside the array.

(defun verina-basic-69-nth-default-zero (index a)
  (if (and
       (natp index)
       (< index (len a)))
      (nth index a)
    0))

;; This is exactly the source precondition: some natural index within the
;; array contains the target integer.

(defun-sk verina-basic-69-linear-search-precond (a e)
  (exists (i)
    (and
     (natp i)
     (< i (len a))
     (equal
      (verina-basic-69-nth-default-zero i a)
      e))))

;; REMAINING is the suffix beginning at the source recursion index INDEX.
;; Equality returns INDEX immediately; otherwise the exact source computation
;; continues at the next natural index. Exhausting the array returns zero.

(defun verina-basic-69-linear-search-aux-loop
    (remaining e index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (equal (car remaining) e)
          index
        (verina-basic-69-linear-search-aux-loop
         (cdr remaining)
         e
         (+ index 1)))
    0))

;; For every source-typed natural N, NTHCDR selects exactly the suffix inspected
;; by linearSearchAux. The out-of-bounds branch and the worker's exhausted
;; branch both reproduce the source result zero.

(defun verina-basic-69-linear-search-aux (a e n)
  (if (and
       (natp n)
       (< n (len a)))
      (verina-basic-69-linear-search-aux-loop
       (nthcdr n a)
       e
       n)
    0))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. The executable program invokes the translated helper at zero.

(defun verina-basic-69-linear-search (a e)
  (verina-basic-69-linear-search-aux a e 0))

;; This predicate preserves the source postcondition's universal Nat binder
;; and states that no index strictly before RESULT contains E.

(defun-sk verina-basic-69-no-target-before-p
    (a e result)
  (forall (k)
    (implies
     (and
      (natp k)
      (< k result))
     (not
      (equal
       (verina-basic-69-nth-default-zero k a)
       e)))))

;; This is the complete source postcondition. The proof-valued precondition
;; argument is unused and therefore erased.

(defun verina-basic-69-linear-search-postcond
    (a e result)
  (and
   (verina-basic-69-int-array-p a)
   (integerp e)
   (natp result)
   (< result (len a))
   (equal
    (verina-basic-69-nth-default-zero result a)
    e)
   (verina-basic-69-no-target-before-p
    a
    e
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int and Int domains, assumes exactly the existential
;; source precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-69-linear-search-spec-satisfied-statement
    ()
  (forall (a e)
    (implies
     (and
      (verina-basic-69-int-array-p a)
      (integerp e)
      (verina-basic-69-linear-search-precond a e))
     (verina-basic-69-linear-search-postcond
      a
      e
      (verina-basic-69-linear-search a e)))))

(value-triple :itpeval-statement-checked)
:q
