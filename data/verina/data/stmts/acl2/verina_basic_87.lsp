;; Statement-only formalization of VERINA corpus artifact verina_basic_87,
;; catalog title "SelectionSort": the deterministic selection-sort program
;; returns a nondecreasing integer array that is a permutation of its input.
;; This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-87-integer-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-87-integer-array-p
        (cdr a)))
    (equal a nil)))

;; The source precondition is True. The Array Int binder domain remains
;; explicit in the final correctness proposition.

(defun verina-basic-87-selection-sort-precond (a)
  (declare (ignore a))
  t)

;; Array.get! on Array Int returns the indexed entry when present and the
;; inhabited integer default zero otherwise.

(defun verina-basic-87-array-read (index a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp a)
        (if (zp index)
            (car a)
          (verina-basic-87-array-read
           (- index 1)
           (cdr a)))
      0)))

;; Array.set! replaces an in-bounds entry and leaves the array unchanged when
;; its natural index is outside the array.

(defun verina-basic-87-array-set
    (index value a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      a
    (if (consp a)
        (if (zp index)
            (cons value (cdr a))
          (cons
           (car a)
           (verina-basic-87-array-set
            (- index 1)
            value
            (cdr a))))
      nil)))

;; This loop is the foldl over List.range (finish - start). OFFSET is the
;; current range element, FUEL is truncated Nat subtraction finish-start, and
;; MIN-INDEX is the fold accumulator.

(defun verina-basic-87-find-min-index-loop
    (arr start offset fuel min-index)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      min-index
    (let ((current-index (+ start offset)))
      (verina-basic-87-find-min-index-loop
       arr
       start
       (+ offset 1)
       (- fuel 1)
       (if (< (verina-basic-87-array-read
               current-index
               arr)
              (verina-basic-87-array-read
               min-index
               arr))
           current-index
         min-index)))))

;; This preserves the complete source findMinIndexInRange helper on its typed
;; Array Int and Nat arguments, including get! defaulting behavior.

(defun verina-basic-87-find-min-index-in-range
    (arr start finish)
  (verina-basic-87-find-min-index-loop
   arr
   start
   0
   (nfix (- finish start))
   start))

;; This is the source swap helper: both indices must be in bounds and distinct;
;; otherwise the input array is returned unchanged. The two set! operations
;; use the original values in exactly the source order.

(defun verina-basic-87-swap (a i j)
  (if (and
       (natp i)
       (natp j)
       (< i (len a))
       (< j (len a))
       (not (equal i j)))
      (let* ((temp
              (verina-basic-87-array-read i a))
             (a-prime
              (verina-basic-87-array-set
               i
               (verina-basic-87-array-read j a)
               a)))
        (verina-basic-87-array-set
         j
         temp
         a-prime))
    a))

;; The source first fixes List.range a.size, then folds over its indices. FUEL
;; is that fixed initial size and FINISH is the captured outer a.size used by
;; every findMinIndexInRange call.

(defun verina-basic-87-selection-sort-loop
    (arr index fuel finish)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      arr
    (let* ((min-index
            (verina-basic-87-find-min-index-in-range
             arr
             index
             finish))
           (next-array
            (verina-basic-87-swap
             arr
             index
             min-index)))
      (verina-basic-87-selection-sort-loop
       next-array
       (+ index 1)
       (- fuel 1)
       finish))))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. This function is the exact executable outer fold.

(defun verina-basic-87-selection-sort (a)
  (let ((size (len a)))
    (verina-basic-87-selection-sort-loop
     a
     0
     size
     size)))

;; List.Pairwise (fun x y => x <= y) requires each head to be at most every
;; later element and recursively imposes the same condition on the tail.

(defun verina-basic-87-head-at-most-all-p
    (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (<= value (car xs))
       (verina-basic-87-head-at-most-all-p
        value
        (cdr xs)))
    (equal xs nil)))

(defun verina-basic-87-pairwise-nondecreasing-p
    (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (verina-basic-87-head-at-most-all-p
        (car xs)
        (cdr xs))
       (verina-basic-87-pairwise-nondecreasing-p
        (cdr xs)))
    (equal xs nil)))

;; Removing one matching occurrence at each recursive step gives exact
;; finite-list multiset equality, including multiplicities, and hence
;; List.isPerm.

(defun verina-basic-87-remove-first
    (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal value (car xs))
          (cdr xs)
        (cons
         (car xs)
         (verina-basic-87-remove-first
          value
          (cdr xs))))
    nil))

(defun verina-basic-87-permutation-p
    (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (member-equal (car left) right)
       (verina-basic-87-permutation-p
        (cdr left)
        (verina-basic-87-remove-first
         (car left)
         right)))
    (equal right nil)))

;; This is the complete source postcondition. The proof-valued precondition
;; argument is erased, while the Array Int types are represented explicitly.

(defun verina-basic-87-selection-sort-postcond
    (a result)
  (and
   (verina-basic-87-integer-array-p a)
   (verina-basic-87-integer-array-p result)
   (verina-basic-87-pairwise-nondecreasing-p
    result)
   (verina-basic-87-permutation-p
    a
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact
;; executable SelectionSort result.

(defun-sk
    verina-basic-87-selection-sort-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-87-integer-array-p a)
      (verina-basic-87-selection-sort-precond a))
     (verina-basic-87-selection-sort-postcond
      a
      (verina-basic-87-selection-sort a)))))

(value-triple :itpeval-statement-checked)
:q
