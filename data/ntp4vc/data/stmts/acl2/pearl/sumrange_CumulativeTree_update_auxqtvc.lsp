;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sumrange_CumulativeTree_update_auxqtvc: the cumulative range-sum tree
;; point-update verification condition, including recursive-call bounds,
;; rebuilt-tree intervals, and the updated tree invariant. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Proper finite integer lists represent Why3 arrays of mathematical integers.

(defun ctu-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (ctu-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat sends negative integers to zero, and the exported total lookup
;; returns the integer default zero outside the list.

(defun ctu-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ctu-nth-int (index xs)
  (let ((value
         (nth
          (ctu-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; List.set leaves the list unchanged when its natural-number index is outside
;; the list.

(defun ctu-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (zp index)
          (cons value (cdr xs))
        (cons
         (car xs)
         (ctu-list-set
          (cdr xs)
          (- index 1)
          value)))
    nil))

;; This is ArraySum.sum on the source-valid half-open interval [LOWER, UPPER).

(defun ctu-range-sum (xs lower upper)
  (declare
   (xargs :measure
          (nfix (- upper lower))))
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (+
       (ctu-nth-int lower xs)
       (ctu-range-sum xs (+ lower 1) upper))
    0))

;; Why3 ComputerDivision.div truncates integer quotients toward zero.

(defun ctu-tdiv (numerator denominator)
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

(defun ctu-indexes (low high isum)
  (list :ctu-indexes low high isum))

(defun ctu-indexes-shape-p (indexes)
  (and
   (true-listp indexes)
   (equal (len indexes) 4)
   (equal (car indexes) :ctu-indexes)))

(defun ctu-indexes-p (indexes)
  (and
   (ctu-indexes-shape-p indexes)
   (integerp (cadr indexes))
   (integerp (caddr indexes))
   (integerp (cadddr indexes))))

(defun ctu-indexes-low (indexes)
  (cadr indexes))

(defun ctu-indexes-high (indexes)
  (caddr indexes))

(defun ctu-indexes-isum (indexes)
  (cadddr indexes))

(defun ctu-leaf (indexes)
  (list :ctu-leaf indexes))

(defun ctu-node (indexes left right)
  (list :ctu-node indexes left right))

(defun ctu-leaf-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 2)
   (equal (car tree) :ctu-leaf)))

(defun ctu-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :ctu-node)))

(defun ctu-tree-indexes (tree)
  (cadr tree))

(defun ctu-tree-left (tree)
  (caddr tree))

(defun ctu-tree-right (tree)
  (cadddr tree))

(defun ctu-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((ctu-leaf-shape-p tree)
    (ctu-indexes-p (ctu-tree-indexes tree)))
   ((ctu-node-shape-p tree)
    (and
     (ctu-indexes-p (ctu-tree-indexes tree))
     (ctu-tree-p (ctu-tree-left tree))
     (ctu-tree-p (ctu-tree-right tree))))
   (t nil)))

;; These are the source predicates is_indexes_for and is_tree_for.

(defun ctu-is-indexes-for-p
    (indexes array lower upper)
  (and
   (ctu-indexes-p indexes)
   (ctu-integer-list-p array)
   (integerp lower)
   (integerp upper)
   (equal (ctu-indexes-low indexes) lower)
   (equal (ctu-indexes-high indexes) upper)
   (<= 0 lower)
   (< lower upper)
   (<= upper (len array))
   (equal
    (ctu-indexes-isum indexes)
    (ctu-range-sum array lower upper))))

(defun ctu-is-tree-for-p
    (tree array lower upper)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((ctu-leaf-shape-p tree)
    (and
     (ctu-is-indexes-for-p
      (ctu-tree-indexes tree)
      array lower upper)
     (equal upper (+ lower 1))))
   ((ctu-node-shape-p tree)
    (let* ((indexes (ctu-tree-indexes tree))
           (left (ctu-tree-left tree))
           (right (ctu-tree-right tree))
           (middle
            (ctu-indexes-high
             (ctu-tree-indexes left))))
      (and
       (ctu-is-indexes-for-p
        indexes array lower upper)
       (equal
        lower
        (ctu-indexes-low
         (ctu-tree-indexes left)))
       (equal
        upper
        (ctu-indexes-high
         (ctu-tree-indexes right)))
       (equal
        middle
        (ctu-indexes-low
         (ctu-tree-indexes right)))
       (< lower middle)
       (< middle upper)
       (equal
        middle
        (ctu-tdiv (+ lower upper) 2))
       (ctu-is-tree-for-p
        left array lower middle)
       (ctu-is-tree-for-p
        right array middle upper))))
   (t nil)))

;; This preserves the repeated source match asserting that the selected
;; recursive argument is one of the current node's two children.

(defun ctu-child-p (tree child)
  (and
   (ctu-node-shape-p tree)
   (or
    (equal (ctu-tree-left tree) child)
    (equal (ctu-tree-right tree) child))))

;; The first generated conjunct supplies the invariant and bounds required by
;; the recursive call selected at a node. It is True at a leaf.

(defun ctu-selected-call-obligation-p
    (tree array index)
  (if (ctu-leaf-shape-p tree)
      t
    (let ((left (ctu-tree-left tree))
          (right (ctu-tree-right tree)))
      (if (<
           index
           (ctu-indexes-high
            (ctu-tree-indexes left)))
          (and
           (ctu-child-p tree left)
           (ctu-is-tree-for-p
            left
            array
            (ctu-indexes-low
             (ctu-tree-indexes left))
            (ctu-indexes-high
             (ctu-tree-indexes left)))
           (<=
            (ctu-indexes-low
             (ctu-tree-indexes left))
            index)
           (<
            index
            (ctu-indexes-high
             (ctu-tree-indexes left))))
        (and
         (ctu-child-p tree right)
         (ctu-is-tree-for-p
          right
          array
          (ctu-indexes-low
           (ctu-tree-indexes right))
          (ctu-indexes-high
           (ctu-tree-indexes right)))
         (<=
          (ctu-indexes-low
           (ctu-tree-indexes right))
          index)
         (<
          index
          (ctu-indexes-high
           (ctu-tree-indexes right))))))))

(defun ctu-updated-indexes
    (indexes array index value)
  (ctu-indexes
   (ctu-indexes-low indexes)
   (ctu-indexes-high indexes)
   (+
    (ctu-indexes-isum indexes)
    (- value (ctu-nth-int index array)))))

;; In each node branch the recursive replacement subtree remains
;; existentially quantified inside the body-result premise.

(defun-sk ctu-left-result-premise-p
    (indexes left right array index value updated delta)
  (exists (new-left)
    (and
     (ctu-tree-p new-left)
     (equal
      (ctu-indexes-low
       (ctu-tree-indexes new-left))
      (ctu-indexes-low
       (ctu-tree-indexes left)))
     (equal
      (ctu-indexes-high
       (ctu-tree-indexes new-left))
      (ctu-indexes-high
       (ctu-tree-indexes left)))
     (ctu-is-tree-for-p
      new-left
      (ctu-list-set
       array
       (ctu-int-to-nat index)
       value)
      (ctu-indexes-low
       (ctu-tree-indexes new-left))
      (ctu-indexes-high
       (ctu-tree-indexes new-left)))
     (equal
      updated
      (ctu-node
       (ctu-updated-indexes
        indexes array index value)
       new-left
       right))
     (equal
      delta
      (- value (ctu-nth-int index array))))))

(defun-sk ctu-right-result-premise-p
    (indexes left right array index value updated delta)
  (exists (new-right)
    (and
     (ctu-tree-p new-right)
     (equal
      (ctu-indexes-low
       (ctu-tree-indexes new-right))
      (ctu-indexes-low
       (ctu-tree-indexes right)))
     (equal
      (ctu-indexes-high
       (ctu-tree-indexes new-right))
      (ctu-indexes-high
       (ctu-tree-indexes right)))
     (ctu-is-tree-for-p
      new-right
      (ctu-list-set
       array
       (ctu-int-to-nat index)
       value)
      (ctu-indexes-low
       (ctu-tree-indexes new-right))
      (ctu-indexes-high
       (ctu-tree-indexes new-right)))
     (equal
      updated
      (ctu-node
       (ctu-updated-indexes
        indexes array index value)
       left
       new-right))
     (equal
      delta
      (- value (ctu-nth-int index array))))))

(defun ctu-result-premise-p
    (tree array index value updated delta)
  (cond
   ((ctu-leaf-shape-p tree)
    (let ((indexes (ctu-tree-indexes tree)))
      (and
       (equal
        updated
        (ctu-leaf
         (ctu-indexes
          (ctu-indexes-low indexes)
          (ctu-indexes-high indexes)
          value)))
       (equal
        delta
        (- value
           (ctu-indexes-isum indexes))))))
   ((ctu-node-shape-p tree)
    (let ((indexes (ctu-tree-indexes tree))
          (left (ctu-tree-left tree))
          (right (ctu-tree-right tree)))
      (if (<
           index
           (ctu-indexes-high
            (ctu-tree-indexes left)))
          (ctu-left-result-premise-p
           indexes left right
           array index value updated delta)
        (ctu-right-result-premise-p
         indexes left right
         array index value updated delta))))
   (t nil)))

(defun ctu-result-conclusion-p
    (tree array index value updated delta)
  (and
   (equal
    delta
    (- value (ctu-nth-int index array)))
   (equal
    (ctu-indexes-low
     (ctu-tree-indexes updated))
    (ctu-indexes-low
     (ctu-tree-indexes tree)))
   (equal
    (ctu-indexes-high
     (ctu-tree-indexes updated))
    (ctu-indexes-high
     (ctu-tree-indexes tree)))
   (ctu-is-tree-for-p
    updated
    (ctu-list-set
     array
     (ctu-int-to-nat index)
     value)
    (ctu-indexes-low
     (ctu-tree-indexes updated))
    (ctu-indexes-high
     (ctu-tree-indexes updated)))))

;; UPDATED and DELTA retain their source universal quantifiers over the full
;; tree and mathematical-integer domains.

(defun-sk ctu-all-results-correct-p
    (tree array index value)
  (forall (updated delta)
    (implies
     (and
      (ctu-tree-p updated)
      (integerp delta))
     (implies
      (ctu-result-premise-p
       tree array index value updated delta)
      (ctu-result-conclusion-p
       tree array index value updated delta)))))

;; The arguments encode the source theorem's universally quantified typed
;; parameters. Its three named assumptions form the antecedent, while both
;; generated conclusion conjuncts and all nested quantifier scopes are kept.

(defun
  ntp4vc-pearl-sumrange-cumulativetree-update-auxqtvc-statement
  (tree array index value)
  (implies
   (and
    (ctu-tree-p tree)
    (ctu-integer-list-p array)
    (integerp index)
    (integerp value)
    (ctu-is-tree-for-p
     tree
     array
     (ctu-indexes-low
      (ctu-tree-indexes tree))
     (ctu-indexes-high
      (ctu-tree-indexes tree)))
    (<=
     (ctu-indexes-low
      (ctu-tree-indexes tree))
     index)
    (<
     index
     (ctu-indexes-high
      (ctu-tree-indexes tree))))
   (and
    (ctu-selected-call-obligation-p
     tree array index)
    (ctu-all-results-correct-p
     tree array index value))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
