;; Statement-only formalization of VERINA corpus artifact verina_basic_70,
;; catalog title "LinearSearch3": under the assumption that an integer array
;; has an element satisfying an arbitrary Boolean predicate, a deterministic
;; left-to-right scan returns the first such index. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-70-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-70-int-array-p (cdr a)))
    (equal a nil)))

;; DEFSTUB is ACL2's conservative interface for the arbitrary source
;; parameter P : Int -> Bool. Boolean normalization identifies NIL with false
;; and every non-NIL result with true; this ranges over exactly all Boolean
;; predicates on the integers.

(defstub verina-basic-70-p (x) t)

(defun verina-basic-70-p-holds (x)
  (if (verina-basic-70-p x)
      t
    nil))

;; Array.get! on Array Int returns the in-bounds entry and the inhabited
;; integer default zero outside the array.

(defun verina-basic-70-nth-default-zero (index a)
  (if (and
       (natp index)
       (< index (len a)))
      (nth index a)
    0))

;; This is exactly the source precondition: some natural index within the
;; array has an element for which P is true.

(defun-sk verina-basic-70-linear-search3-precond (a)
  (exists (i)
    (and
     (natp i)
     (< i (len a))
     (verina-basic-70-p-holds
      (verina-basic-70-nth-default-zero i a)))))

;; REMAINING is the suffix beginning at the source loop index INDEX. A true
;; predicate result returns INDEX immediately; otherwise the exact source
;; computation advances one index. Exhausting the array returns zero.

(defun verina-basic-70-linear-search3-loop
    (remaining index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (verina-basic-70-p-holds (car remaining))
          index
        (verina-basic-70-linear-search3-loop
         (cdr remaining)
         (+ index 1)))
    0))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. Starting the exact loop at natural index zero reproduces the
;; executable Lean implementation.

(defun verina-basic-70-linear-search3 (a)
  (verina-basic-70-linear-search3-loop a 0))

;; This predicate preserves the source postcondition's universal Nat binder:
;; no index strictly before RESULT has an element for which P is true.

(defun-sk verina-basic-70-no-match-before-p
    (a result)
  (forall (k)
    (implies
     (and
      (natp k)
      (< k result))
     (not
      (verina-basic-70-p-holds
       (verina-basic-70-nth-default-zero k a))))))

;; This is the complete source postcondition. The proof-valued precondition
;; argument is unused and therefore erased.

(defun verina-basic-70-linear-search3-postcond
    (a result)
  (and
   (verina-basic-70-int-array-p a)
   (natp result)
   (< result (len a))
   (verina-basic-70-p-holds
    (verina-basic-70-nth-default-zero result a))
   (verina-basic-70-no-match-before-p
    a
    result)))

;; This predicate is the unproved final correctness proposition. The DEFSTUB
;; above makes it generic over every Boolean predicate on Int; it quantifies
;; over the complete Array Int domain, assumes exactly the existential source
;; precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-70-linear-search3-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-70-int-array-p a)
      (verina-basic-70-linear-search3-precond a))
     (verina-basic-70-linear-search3-postcond
      a
      (verina-basic-70-linear-search3 a)))))

(value-triple :itpeval-statement-checked)
:q
