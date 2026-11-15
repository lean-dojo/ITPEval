;; Statement-only formalization of VERINA corpus artifact verina_basic_84,
;; catalog title "replace": a deterministic integer-array program replaces
;; every entry greater than an integer threshold with negative one and leaves
;; every other entry unchanged. This file contains no proof.

(in-package "ACL2")

;; A Lean Array Int is represented exactly by its finite sequence of entries:
;; a proper ACL2 list whose elements range over all integers.

(defun verina-basic-84-integer-array-p (array)
  (declare (xargs :measure (acl2-count array)))
  (if (consp array)
      (and
       (integerp (car array))
       (verina-basic-84-integer-array-p
        (cdr array)))
    (equal array nil)))

;; The source precondition is True. The Array Int and Int binder domains
;; remain explicit in the final correctness proposition.

(defun verina-basic-84-replace-precond (arr k)
  (declare (ignore arr k))
  t)

;; Array.get! on Array Int returns the indexed entry when present and the
;; inhabited integer default zero otherwise.

(defun verina-basic-84-array-read
    (index array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp array)
        (if (zp index)
            (car array)
          (verina-basic-84-array-read
           (- index 1)
           (cdr array)))
      0)))

;; Array.set! replaces an in-bounds entry and leaves the array unchanged when
;; its natural index is outside the array.

(defun verina-basic-84-array-set
    (index value array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      array
    (if (consp array)
        (if (zp index)
            (cons value (cdr array))
          (cons
           (car array)
           (verina-basic-84-array-set
            (- index 1)
            value
            (cdr array))))
      nil)))

;; This is exact natural-number suffix removal. It provides the unprocessed
;; suffix of OLD-ARR beginning at the source loop's current index.

(defun verina-basic-84-drop
    (count array)
  (declare (xargs :measure (nfix count)))
  (if (and
       (natp count)
       (< 0 count)
       (consp array))
      (verina-basic-84-drop
       (- count 1)
       (cdr array))
    array))

;; REMAINING is the suffix of OLD-ARR beginning at INDEX. Every recursive step
;; reads the original entry, conditionally writes negative one to ACC at the
;; same index, and advances exactly as the source replace_loop helper does.

(defun verina-basic-84-replace-loop-scan
    (old-arr k index acc remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-basic-84-replace-loop-scan
       old-arr
       k
       (+ index 1)
       (if (> (verina-basic-84-array-read
               index
               old-arr)
              k)
           (verina-basic-84-array-set
            index
            -1
            acc)
         acc)
       (cdr remaining))
    acc))

;; This preserves the complete source helper signature and computation on its
;; typed Array Int, Int, Nat, and Array Int arguments.

(defun verina-basic-84-replace-loop
    (old-arr k index acc)
  (verina-basic-84-replace-loop-scan
   old-arr
   k
   index
   acc
   (verina-basic-84-drop index old-arr)))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The original array is also the initial accumulator at index
;; zero, exactly as in the source implementation.

(defun verina-basic-84-replace (arr k)
  (verina-basic-84-replace-loop
   arr
   k
   0
   arr))

;; These predicates preserve the source postcondition's two universal Nat
;; quantifiers, their in-bounds assumptions, and their conditional clauses.

(defun-sk verina-basic-84-greater-entries-replaced-p
    (arr k result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len arr)))
     (implies
      (> (verina-basic-84-array-read i arr)
         k)
      (equal
       (verina-basic-84-array-read i result)
       -1)))))

(defun-sk verina-basic-84-other-entries-unchanged-p
    (arr k result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len arr)))
     (implies
      (<= (verina-basic-84-array-read i arr)
          k)
      (equal
       (verina-basic-84-array-read i result)
       (verina-basic-84-array-read i arr))))))

;; This is the complete source postcondition, including result size and both
;; pointwise threshold cases. The unused proof-valued precondition argument
;; is erased.

(defun verina-basic-84-replace-postcond
    (arr k result)
  (and
   (verina-basic-84-integer-array-p arr)
   (integerp k)
   (verina-basic-84-integer-array-p result)
   (equal (len result) (len arr))
   (verina-basic-84-greater-entries-replaced-p
    arr
    k
    result)
   (verina-basic-84-other-entries-unchanged-p
    arr
    k
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array and integer threshold, assumes exactly the
;; source True precondition, and applies the complete postcondition to the
;; exact executable result.

(defun-sk
    verina-basic-84-replace-spec-satisfied-statement
    ()
  (forall (arr k)
    (implies
     (and
      (verina-basic-84-integer-array-p arr)
      (integerp k)
      (verina-basic-84-replace-precond
       arr
       k))
     (verina-basic-84-replace-postcond
      arr
      k
      (verina-basic-84-replace arr k)))))

(value-triple :itpeval-statement-checked)
:q
