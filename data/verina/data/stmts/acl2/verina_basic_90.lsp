;; Statement-only formalization of VERINA corpus artifact verina_basic_90,
;; catalog title "SlopeSearch": a deterministic top-right search of a
;; nonempty rectangular integer matrix sorted by rows and columns returns a
;; matching position or (-1, -1). This file contains no proof.

(in-package "ACL2")

;; A finite Lean Array (Array Int) is represented bijectively by a proper
;; ACL2 list of proper integer lists.

(defun verina-basic-90-int-array-p (row)
  (declare (xargs :measure (acl2-count row)))
  (if (consp row)
      (and
       (integerp (car row))
       (verina-basic-90-int-array-p (cdr row)))
    (equal row nil)))

(defun verina-basic-90-int-matrix-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (verina-basic-90-int-array-p (car a))
       (verina-basic-90-int-matrix-p (cdr a)))
    (equal a nil)))

;; These predicates are exactly List.Pairwise equality on row sizes: each
;; head row has the same length as every later row, recursively.

(defun verina-basic-90-head-length-equals-all-p
    (row-length remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (equal row-length (len (car remaining)))
       (verina-basic-90-head-length-equals-all-p
        row-length
        (cdr remaining)))
    (equal remaining nil)))

(defun verina-basic-90-pairwise-equal-row-lengths-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (verina-basic-90-head-length-equals-all-p
        (len (car a))
        (cdr a))
       (verina-basic-90-pairwise-equal-row-lengths-p
        (cdr a)))
    (equal a nil)))

;; These predicates are exactly List.Pairwise (fun x y => x <= y): each head
;; is at most every later integer, recursively for every suffix.

(defun verina-basic-90-head-at-most-all-p
    (head remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (<= head (car remaining))
       (verina-basic-90-head-at-most-all-p
        head
        (cdr remaining)))
    (equal remaining nil)))

(defun verina-basic-90-pairwise-nondecreasing-p (values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (and
       (verina-basic-90-head-at-most-all-p
        (car values)
        (cdr values))
       (verina-basic-90-pairwise-nondecreasing-p
        (cdr values)))
    (equal values nil)))

;; Array.get! on Array Int returns the indexed entry when present and the
;; inhabited integer default zero otherwise.

(defun verina-basic-90-array-read (index row)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp row)
        (if (zp index)
            (car row)
          (verina-basic-90-array-read
           (- index 1)
           (cdr row)))
      0)))

;; Mapping the source defaulting read at INDEX over all rows gives exactly the
;; column list used by the source column-sortedness precondition.

(defun verina-basic-90-column-values (index a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (cons
       (verina-basic-90-array-read
        index
        (car a))
       (verina-basic-90-column-values
        index
        (cdr a)))
    nil))

;; Starting at column zero for the first row's length reproduces
;; (List.range (a[0]!.size)).all and its Pairwise test for every column.

(defun verina-basic-90-all-columns-nondecreasing-p
    (a index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (verina-basic-90-pairwise-nondecreasing-p
      (verina-basic-90-column-values index a))
     (verina-basic-90-all-columns-nondecreasing-p
      a
      (+ index 1)
      (- remaining 1)))))

(defun verina-basic-90-all-rows-nondecreasing-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (verina-basic-90-pairwise-nondecreasing-p
        (car a))
       (verina-basic-90-all-rows-nondecreasing-p
        (cdr a)))
    (equal a nil)))

;; This is exactly the source precondition after Array.size is represented by
;; list length. KEY is unused by the source precondition.

(defun verina-basic-90-slope-search-precond (a key)
  (declare (ignore key))
  (and
   (consp a)
   (consp (car a))
   (verina-basic-90-pairwise-equal-row-lengths-p a)
   (verina-basic-90-all-rows-nondecreasing-p a)
   (verina-basic-90-all-columns-nondecreasing-p
    a
    0
    (len (car a)))))

;; Lean Int.toNat maps every negative integer to zero and preserves every
;; nonnegative integer.

(defun verina-basic-90-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

;; Array.get! on Array (Array Int) returns the indexed row when present and
;; the inhabited empty-array default otherwise.

(defun verina-basic-90-row-read (index a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      nil
    (if (consp a)
        (if (zp index)
            (car a)
          (verina-basic-90-row-read
           (- index 1)
           (cdr a)))
      nil)))

;; This is the complete source get2d helper, including both Int.toNat
;; conversions and both inhabited Array.get! defaults.

(defun verina-basic-90-get2d (a i j)
  (verina-basic-90-array-read
   (verina-basic-90-int-to-nat j)
   (verina-basic-90-row-read
    (verina-basic-90-int-to-nat i)
    a)))

;; An Int x Int result is represented by a dotted pair whose car and cdr are
;; arbitrary ACL2 integers.

(defun verina-basic-90-int-pair-p (result)
  (and
   (consp result)
   (integerp (car result))
   (integerp (cdr result))))

;; This fuel recursion reproduces the source-local AUX exactly. The first
;; branch returns (-1, -1) at zero fuel; the remaining guards, comparisons,
;; coordinate updates, and fuel decrement occur in the source order.

(defun verina-basic-90-slope-search-aux
    (a key m n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (cons -1 -1)
    (if (or
         (>= m (len a))
         (< n 0))
        (cons -1 -1)
      (let ((entry
             (verina-basic-90-get2d a m n)))
        (if (equal entry key)
            (cons m n)
          (if (< entry key)
              (verina-basic-90-slope-search-aux
               a
               key
               (+ m 1)
               n
               (- fuel 1))
            (verina-basic-90-slope-search-aux
             a
             key
             m
             (- n 1)
             (- fuel 1))))))))

;; Natural subtraction in cols - 1 is represented by NFIX. The proof-valued
;; precondition argument is computationally irrelevant and is erased.

(defun verina-basic-90-slope-search (a key)
  (let* ((rows (len a))
         (cols
          (if (< 0 rows)
              (len (car a))
            0)))
    (verina-basic-90-slope-search-aux
     a
     key
     0
     (nfix (- cols 1))
     (+ rows cols))))

;; These recursions are the nested Array.all expression asserting that no
;; matrix entry equals KEY.

(defun verina-basic-90-row-excludes-key-p (row key)
  (declare (xargs :measure (acl2-count row)))
  (if (consp row)
      (and
       (not (equal (car row) key))
       (verina-basic-90-row-excludes-key-p
        (cdr row)
        key))
    (equal row nil)))

(defun verina-basic-90-matrix-excludes-key-p (a key)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (verina-basic-90-row-excludes-key-p
        (car a)
        key)
       (verina-basic-90-matrix-excludes-key-p
        (cdr a)
        key))
    (equal a nil)))

;; This is the complete source postcondition. The first disjunct gives an
;; in-bounds matching coordinate; the second requires exactly (-1, -1) and
;; absence of KEY from every row.

(defun verina-basic-90-slope-search-postcond
    (a key result)
  (and
   (verina-basic-90-int-matrix-p a)
   (integerp key)
   (verina-basic-90-int-pair-p result)
   (let ((m (car result))
         (n (cdr result)))
     (or
      (and
       (<= 0 m)
       (< m (len a))
       (<= 0 n)
       (< n (len (car a)))
       (equal
        (verina-basic-90-get2d a m n)
        key))
      (and
       (equal m -1)
       (equal n -1)
       (verina-basic-90-matrix-excludes-key-p
        a
        key))))))

;; This predicate is the unproved final correctness proposition. It
;; quantifies over every finite integer matrix and integer key, assumes exactly
;; the source rectangular row/column sortedness precondition, and applies the
;; full postcondition to the exact executable result.

(defun-sk
    verina-basic-90-slope-search-spec-satisfied-statement
    ()
  (forall (a key)
    (implies
     (and
      (verina-basic-90-int-matrix-p a)
      (integerp key)
      (verina-basic-90-slope-search-precond
       a
       key))
     (verina-basic-90-slope-search-postcond
      a
      key
      (verina-basic-90-slope-search
       a
       key)))))

(value-triple :itpeval-statement-checked)
:q
