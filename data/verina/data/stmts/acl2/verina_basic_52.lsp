;; Statement-only formalization of VERINA corpus artifact verina_basic_52,
;; catalog title "BubbleSort": the executable bubble-sort program returns a
;; nondecreasing integer array that is a permutation of its input. This file
;; contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-52-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-52-int-array-p (cdr a)))
    (equal a nil)))

;; The source precondition is True. The Array Int domain remains explicit in
;; the final correctness proposition.

(defun verina-basic-52-bubble-sort-precond (a)
  (declare (ignore a))
  t)

;; Array.get! on Array Int returns the indexed entry when it is present and
;; the inhabited integer default zero otherwise.

(defun verina-basic-52-array-read (index a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp a)
        (if (zp index)
            (car a)
          (verina-basic-52-array-read
           (- index 1)
           (cdr a)))
      0)))

;; Array.set! replaces an in-bounds entry and leaves the array unchanged when
;; the natural index is out of bounds.

(defun verina-basic-52-array-set (index value a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      a
    (if (consp a)
        (if (zp index)
            (cons value (cdr a))
          (cons
           (car a)
           (verina-basic-52-array-set
            (- index 1)
            value
            (cdr a))))
      nil)))

;; This is the exact ordered pair of reads and writes in the source swap
;; helper, including the total get! and set! behavior at arbitrary Nat indices.

(defun verina-basic-52-swap (a i j)
  (let* ((temp
          (verina-basic-52-array-read i a))
         (a1
          (verina-basic-52-array-set
           i
           (verina-basic-52-array-read j a)
           a)))
    (verina-basic-52-array-set j temp a1)))

;; For natural J and I, I-J fuel units are exactly the number of source
;; recursive calls before J reaches I. Thus fuel cannot expire while J < I,
;; and this function computes bubbleInner without admitting extra outcomes.

(defun verina-basic-52-bubble-inner-fuel
    (j i a fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or
       (zp fuel)
       (not (natp j))
       (not (natp i))
       (not (< j i)))
      a
    (let* ((next-index (+ j 1))
           (next-a
            (if (>
                 (verina-basic-52-array-read j a)
                 (verina-basic-52-array-read next-index a))
                (verina-basic-52-swap
                 a
                 j
                 next-index)
              a)))
      (verina-basic-52-bubble-inner-fuel
       next-index
       i
       next-a
       (- fuel 1)))))

(defun verina-basic-52-bubble-inner (j i a)
  (verina-basic-52-bubble-inner-fuel
   j
   i
   a
   (nfix (- i j))))

;; For natural I, I fuel units reproduce the source recursive countdown to
;; zero. Each pass invokes the exact bubbleInner computation before decreasing
;; I, just as in bubbleOuter.

(defun verina-basic-52-bubble-outer-fuel
    (i a fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or
       (zp fuel)
       (not (natp i))
       (not (> i 0)))
      a
    (let ((next-a
           (verina-basic-52-bubble-inner
            0
            i
            a)))
      (verina-basic-52-bubble-outer-fuel
       (- i 1)
       next-a
       (- fuel 1)))))

(defun verina-basic-52-bubble-outer (i a)
  (verina-basic-52-bubble-outer-fuel
   i
   a
   (nfix i)))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. This empty-array branch and initial outer index exactly
;; reproduce the source BubbleSort implementation.

(defun verina-basic-52-bubble-sort (a)
  (if (equal (len a) 0)
      a
    (verina-basic-52-bubble-outer
     (- (len a) 1)
     a)))

;; These predicates are exactly List.Pairwise (fun x y => x <= y): each head
;; is at most every later entry, recursively for every suffix.

(defun verina-basic-52-head-at-most-all-p
    (head remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (<= head (car remaining))
       (verina-basic-52-head-at-most-all-p
        head
        (cdr remaining)))
    (equal remaining nil)))

(defun verina-basic-52-pairwise-nondecreasing-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (verina-basic-52-head-at-most-all-p
        (car a)
        (cdr a))
       (verina-basic-52-pairwise-nondecreasing-p
        (cdr a)))
    (equal a nil)))

;; Removing one matching occurrence at each step gives exact finite-list
;; multiset equality, including duplicate multiplicities, and hence List.isPerm.

(defun verina-basic-52-remove-first (value a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (if (equal value (car a))
          (cdr a)
        (cons
         (car a)
         (verina-basic-52-remove-first
          value
          (cdr a))))
    nil))

(defun verina-basic-52-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (member-equal (car left) right)
       (verina-basic-52-permutation-p
        (cdr left)
        (verina-basic-52-remove-first
         (car left)
         right)))
    (equal right nil)))

;; This is the complete source postcondition. The proof-valued precondition
;; argument is unused and erased.

(defun verina-basic-52-bubble-sort-postcond
    (a result)
  (and
   (verina-basic-52-int-array-p a)
   (verina-basic-52-int-array-p result)
   (verina-basic-52-pairwise-nondecreasing-p result)
   (verina-basic-52-permutation-p result a)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array satisfying the source True precondition and
;; applies the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-52-bubble-sort-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-52-int-array-p a)
      (verina-basic-52-bubble-sort-precond a))
     (verina-basic-52-bubble-sort-postcond
      a
      (verina-basic-52-bubble-sort a)))))

(value-triple :itpeval-statement-checked)
:q
