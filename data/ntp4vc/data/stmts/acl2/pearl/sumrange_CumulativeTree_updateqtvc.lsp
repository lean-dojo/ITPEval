;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sumrange_CumulativeTree_updateqtvc: the cumulative range-sum tree
;; point-update verification condition, preserving the tree interval and
;; establishing the updated-array cell, frame, and tree invariants.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Proper finite integer lists represent Why3 arrays of mathematical integers.

(defun ct-update-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (ct-update-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat sends negative integers to zero, and the exported total lookup
;; returns the integer default zero outside the list.

(defun ct-update-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ct-update-nth-int (index xs)
  (let ((value
         (nth
          (ct-update-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; Source List.set leaves the list unchanged when its natural-number index is
;; outside the list.

(defun ct-update-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (zp index)
          (cons value (cdr xs))
        (cons
         (car xs)
         (ct-update-list-set
          (cdr xs)
          (- index 1)
          value)))
    nil))

;; This is ArraySum.sum on the source-valid half-open interval [LOWER, UPPER).

(defun ct-update-range-sum (xs lower upper)
  (declare
   (xargs :measure
          (nfix (- upper lower))))
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (+
       (ct-update-nth-int lower xs)
       (ct-update-range-sum xs (+ lower 1) upper))
    0))

;; Why3 ComputerDivision.div truncates integer quotients toward zero.

(defun ct-update-tdiv (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor
              (abs numerator)
              (abs denominator))))
        (if (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

;; INDEXES and TREE are exact tagged constructor records for the source
;; datatypes.

(defun ct-update-indexes (low high isum)
  (list :ct-update-indexes low high isum))

(defun ct-update-indexes-shape-p (indexes)
  (and
   (true-listp indexes)
   (equal (len indexes) 4)
   (equal (car indexes) :ct-update-indexes)))

(defun ct-update-indexes-p (indexes)
  (and
   (ct-update-indexes-shape-p indexes)
   (integerp (cadr indexes))
   (integerp (caddr indexes))
   (integerp (cadddr indexes))))

(defun ct-update-indexes-low (indexes)
  (cadr indexes))

(defun ct-update-indexes-high (indexes)
  (caddr indexes))

(defun ct-update-indexes-isum (indexes)
  (cadddr indexes))

(defun ct-update-leaf (indexes)
  (list :ct-update-leaf indexes))

(defun ct-update-node (indexes left right)
  (list :ct-update-node indexes left right))

(defun ct-update-leaf-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 2)
   (equal (car tree) :ct-update-leaf)))

(defun ct-update-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :ct-update-node)))

(defun ct-update-tree-indexes (tree)
  (cadr tree))

(defun ct-update-tree-left (tree)
  (caddr tree))

(defun ct-update-tree-right (tree)
  (cadddr tree))

(defun ct-update-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((ct-update-leaf-shape-p tree)
    (ct-update-indexes-p
     (ct-update-tree-indexes tree)))
   ((ct-update-node-shape-p tree)
    (and
     (ct-update-indexes-p
      (ct-update-tree-indexes tree))
     (ct-update-tree-p
      (ct-update-tree-left tree))
     (ct-update-tree-p
      (ct-update-tree-right tree))))
   (t nil)))

;; These are the source predicates is_indexes_for and is_tree_for.

(defun ct-update-is-indexes-for-p
    (indexes array lower upper)
  (and
   (ct-update-indexes-p indexes)
   (ct-update-integer-list-p array)
   (integerp lower)
   (integerp upper)
   (equal
    (ct-update-indexes-low indexes)
    lower)
   (equal
    (ct-update-indexes-high indexes)
    upper)
   (<= 0 lower)
   (< lower upper)
   (<= upper (len array))
   (equal
    (ct-update-indexes-isum indexes)
    (ct-update-range-sum
     array lower upper))))

(defun ct-update-is-tree-for-p
    (tree array lower upper)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((ct-update-leaf-shape-p tree)
    (and
     (ct-update-is-indexes-for-p
      (ct-update-tree-indexes tree)
      array lower upper)
     (equal upper (+ lower 1))))
   ((ct-update-node-shape-p tree)
    (let* ((indexes
            (ct-update-tree-indexes tree))
           (left
            (ct-update-tree-left tree))
           (right
            (ct-update-tree-right tree))
           (middle
            (ct-update-indexes-high
             (ct-update-tree-indexes left))))
      (and
       (ct-update-is-indexes-for-p
        indexes array lower upper)
       (equal
        lower
        (ct-update-indexes-low
         (ct-update-tree-indexes left)))
       (equal
        upper
        (ct-update-indexes-high
         (ct-update-tree-indexes right)))
       (equal
        middle
        (ct-update-indexes-low
         (ct-update-tree-indexes right)))
       (< lower middle)
       (< middle upper)
       (equal
        middle
        (ct-update-tdiv
         (+ lower upper)
         2))
       (ct-update-is-tree-for-p
        left array lower middle)
       (ct-update-is-tree-for-p
        right array middle upper))))
   (t nil)))

;; Extensional equality between the updated list's total integer-indexed view
;; and Function.update remains quantified over every mathematical integer.

(defun-sk ct-update-set-function-equal-p
    (array index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (ct-update-nth-int
       argument
       (ct-update-list-set
        array
        (ct-update-int-to-nat index)
        value))
      (if (equal argument index)
          value
        (ct-update-nth-int
         argument array))))))

;; This is the source frame condition for every valid index other than the
;; updated one.

(defun-sk ct-update-other-cells-unchanged-p
    (updated-array old-array index)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (and
        (<= 0 k)
        (< k (len updated-array)))
       (not (equal k index)))
      (equal
       (ct-update-nth-int
        k updated-array)
       (ct-update-nth-int
        k old-array))))))

;; The nested length and extensional-update implications are preserved
;; verbatim before the cell, frame, and final tree postconditions.

(defun ct-update-replacement-conclusion-p
    (replacement updated-array old-array index value)
  (and
   (<= 0 index)
   (< index (len old-array))
   (implies
    (equal
     (len updated-array)
     (len old-array))
    (implies
     (ct-update-set-function-equal-p
      old-array index value)
     (and
      (equal
       (ct-update-nth-int
        index updated-array)
       value)
      (ct-update-other-cells-unchanged-p
       updated-array old-array index)
      (ct-update-is-tree-for-p
       replacement
       updated-array
       0
       (len updated-array)))))))

;; The replacement tree remains universally quantified inside the conclusion,
;; exactly as in the source verification condition.

(defun-sk ct-update-all-replacement-trees-p
    (tree array index value)
  (forall (replacement)
    (implies
     (ct-update-tree-p replacement)
     (let ((updated-array
            (ct-update-list-set
             array
             (ct-update-int-to-nat index)
             value)))
       (implies
        (and
         (equal
          (ct-update-indexes-low
           (ct-update-tree-indexes replacement))
          (ct-update-indexes-low
           (ct-update-tree-indexes tree)))
         (equal
          (ct-update-indexes-high
           (ct-update-tree-indexes replacement))
          (ct-update-indexes-high
           (ct-update-tree-indexes tree)))
         (ct-update-is-tree-for-p
          replacement
          updated-array
          (ct-update-indexes-low
           (ct-update-tree-indexes replacement))
          (ct-update-indexes-high
           (ct-update-tree-indexes replacement))))
        (ct-update-replacement-conclusion-p
         replacement
         updated-array
         array
         index
         value))))))

;; The arguments encode the source theorem's universally quantified typed
;; parameters. The antecedent is exactly its three assumptions, and the
;; conclusion preserves all four conjuncts and every inner quantifier.

(defun
  ntp4vc-pearl-sumrange-cumulativetree-updateqtvc-statement
  (index array tree value)
  (implies
   (and
    (integerp index)
    (ct-update-integer-list-p array)
    (ct-update-tree-p tree)
    (integerp value)
    (<= 0 index)
    (< index (len array))
    (ct-update-is-tree-for-p
     tree array 0 (len array)))
   (and
    (ct-update-is-tree-for-p
     tree
     array
     (ct-update-indexes-low
      (ct-update-tree-indexes tree))
     (ct-update-indexes-high
      (ct-update-tree-indexes tree)))
    (<=
     (ct-update-indexes-low
      (ct-update-tree-indexes tree))
     index)
    (<
     index
     (ct-update-indexes-high
      (ct-update-tree-indexes tree)))
    (ct-update-all-replacement-trees-p
     tree array index value))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
