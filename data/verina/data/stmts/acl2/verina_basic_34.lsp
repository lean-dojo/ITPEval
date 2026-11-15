;; Statement-only formalization of VERINA corpus artifact verina_basic_34,
;; catalog title "findEvenNumbers": a deterministic integer-array program
;; extracts exactly the even entries in input order, preserving multiplicity.
;; This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-34-int-array-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (integerp (car arr))
       (verina-basic-34-int-array-p (cdr arr)))
    (equal arr nil)))

;; With positive divisor two, ACL2 MOD and Lean Int.emod agree on every
;; integer, so this is exactly the source Boolean helper isEven.

(defun verina-basic-34-is-even (n)
  (equal (mod n 2) 0))

;; The source precondition is True. The Array Int binder domain remains
;; explicit in the final correctness proposition.

(defun verina-basic-34-find-even-numbers-precond (arr)
  (declare (ignore arr))
  t)

;; ACC is the source fold accumulator. Appending the current even entry is the
;; list representation of Array.push, so this recursion is exactly the source
;; Array.foldl traversal from the empty array. The proof-valued precondition
;; argument is computationally irrelevant and is erased.

(defun verina-basic-34-find-even-numbers-fold (remaining acc)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-basic-34-find-even-numbers-fold
       (cdr remaining)
       (if (verina-basic-34-is-even (car remaining))
           (append acc (cons (car remaining) nil))
         acc))
    acc))

(defun verina-basic-34-find-even-numbers (arr)
  (verina-basic-34-find-even-numbers-fold arr nil))

;; Exact recursive encodings of source list membership, List.count, and
;; List.idxOf. The latter returns the list length when the value is absent.

(defun verina-basic-34-member-p (x values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (or
       (equal x (car values))
       (verina-basic-34-member-p x (cdr values)))
    nil))

(defun verina-basic-34-count (x values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (+
       (if (equal x (car values)) 1 0)
       (verina-basic-34-count x (cdr values)))
    0))

(defun verina-basic-34-idx-of-aux (x remaining index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (equal x (car remaining))
          index
        (verina-basic-34-idx-of-aux
         x
         (cdr remaining)
         (+ index 1)))
    index))

(defun verina-basic-34-idx-of (x values)
  (verina-basic-34-idx-of-aux x values 0))

;; This is result.all from the first source postcondition conjunct. Each output
;; entry is even, occurs in the input, and has the same full-list multiplicity
;; in the result and input.

(defun verina-basic-34-result-all-valid-p
    (remaining result arr)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((x (car remaining)))
        (and
         (verina-basic-34-is-even x)
         (verina-basic-34-member-p x arr)
         (equal
          (verina-basic-34-count x result)
          (verina-basic-34-count x arr))
         (verina-basic-34-result-all-valid-p
          (cdr remaining)
          result
          arr)))
    (equal remaining nil)))

;; This is arr.all from the second source conjunct: every even input entry is
;; present in the result.

(defun verina-basic-34-all-even-inputs-present-p
    (remaining result)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (implies
        (verina-basic-34-is-even (car remaining))
        (verina-basic-34-member-p (car remaining) result))
       (verina-basic-34-all-even-inputs-present-p
        (cdr remaining)
        result))
    (equal remaining nil)))

;; These nested traversals reproduce the two source Array.all calls in the
;; order conjunct. For every input pair x and y, if both are even and x's first
;; input occurrence is no later than y's, the same first-occurrence ordering
;; holds in the result.

(defun verina-basic-34-all-y-order-preserved-p
    (x remaining-y arr result)
  (declare (xargs :measure (acl2-count remaining-y)))
  (if (consp remaining-y)
      (let ((y (car remaining-y)))
        (and
         (implies
          (and
           (verina-basic-34-is-even x)
           (verina-basic-34-is-even y)
           (<=
            (verina-basic-34-idx-of x arr)
            (verina-basic-34-idx-of y arr)))
          (<=
           (verina-basic-34-idx-of x result)
           (verina-basic-34-idx-of y result)))
         (verina-basic-34-all-y-order-preserved-p
          x
          (cdr remaining-y)
          arr
          result)))
    (equal remaining-y nil)))

(defun verina-basic-34-all-order-preserved-p
    (remaining-x arr result)
  (declare (xargs :measure (acl2-count remaining-x)))
  (if (consp remaining-x)
      (and
       (verina-basic-34-all-y-order-preserved-p
        (car remaining-x)
        arr
        arr
        result)
       (verina-basic-34-all-order-preserved-p
        (cdr remaining-x)
        arr
        result))
    (equal remaining-x nil)))

;; This is the complete source postcondition. Its proof-valued True
;; precondition argument is unused and therefore erased.

(defun verina-basic-34-find-even-numbers-postcond
    (arr result)
  (and
   (verina-basic-34-int-array-p arr)
   (verina-basic-34-int-array-p result)
   (verina-basic-34-result-all-valid-p
    result
    result
    arr)
   (verina-basic-34-all-even-inputs-present-p
    arr
    result)
   (verina-basic-34-all-order-preserved-p
    arr
    arr
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int domain, applies the source True precondition,
;; and connects the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-34-find-even-numbers-spec-satisfied-statement
    ()
  (forall (arr)
    (implies
     (and
      (verina-basic-34-int-array-p arr)
      (verina-basic-34-find-even-numbers-precond arr))
     (verina-basic-34-find-even-numbers-postcond
      arr
      (verina-basic-34-find-even-numbers arr)))))

(value-triple :itpeval-statement-checked)
:q
