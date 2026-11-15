;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sumrange_CumulativeTree_tree_of_arrayqtvc: the cumulative range-sum
;; tree construction verification condition, including midpoint descent,
;; recursive subtree contracts, and the final tree invariant. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Proper finite integer lists represent Why3 arrays of mathematical integers.

(defun scta-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (scta-integer-list-p (cdr xs)))
    (equal xs nil)))

(defun scta-nth-int (index xs)
  (let ((value (nth (nfix index) xs)))
    (if (integerp value)
        value
      0)))

;; On source-valid bounds this is exactly ArraySum.sum over [LOWER, UPPER).

(defun scta-range-sum (xs lower upper)
  (declare
   (xargs :measure
          (nfix (- upper lower))))
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (+
       (scta-nth-int (- upper 1) xs)
       (scta-range-sum xs lower (- upper 1)))
    0))

;; Why3 ComputerDivision.div truncates integer quotients toward zero.

(defun scta-tdiv (numerator denominator)
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

(defun scta-midpoint (lower upper)
  (scta-tdiv (+ lower upper) 2))

;; INDEXES and TREE are exact tagged constructor records for the source
;; datatypes. Every source indexes value and finite source tree has one such
;; representation, and the tags keep the constructors disjoint.

(defun scta-indexes (low high isum)
  (list :scta-indexes low high isum))

(defun scta-indexes-shape-p (indexes)
  (and
   (true-listp indexes)
   (equal (len indexes) 4)
   (equal (car indexes) :scta-indexes)))

(defun scta-indexes-p (indexes)
  (and
   (scta-indexes-shape-p indexes)
   (integerp (cadr indexes))
   (integerp (caddr indexes))
   (integerp (cadddr indexes))))

(defun scta-indexes-low (indexes)
  (cadr indexes))

(defun scta-indexes-high (indexes)
  (caddr indexes))

(defun scta-indexes-isum (indexes)
  (cadddr indexes))

(defun scta-leaf (indexes)
  (list :scta-leaf indexes))

(defun scta-node (indexes left right)
  (list :scta-node indexes left right))

(defun scta-leaf-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 2)
   (equal (car tree) :scta-leaf)))

(defun scta-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :scta-node)))

(defun scta-tree-indexes (tree)
  (cadr tree))

(defun scta-tree-left (tree)
  (caddr tree))

(defun scta-tree-right (tree)
  (cadddr tree))

(defun scta-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((scta-leaf-shape-p tree)
    (scta-indexes-p (scta-tree-indexes tree)))
   ((scta-node-shape-p tree)
    (and
     (scta-indexes-p (scta-tree-indexes tree))
     (scta-tree-p (scta-tree-left tree))
     (scta-tree-p (scta-tree-right tree))))
   (t nil)))

(defun scta-is-indexes-for-p
    (indexes array lower upper)
  (and
   (scta-indexes-p indexes)
   (scta-integer-list-p array)
   (integerp lower)
   (integerp upper)
   (equal (scta-indexes-low indexes) lower)
   (equal (scta-indexes-high indexes) upper)
   (<= 0 lower)
   (< lower upper)
   (<= upper (len array))
   (equal
    (scta-indexes-isum indexes)
    (scta-range-sum array lower upper))))

;; This recursive predicate is the source is_tree_for definition, including
;; the exact half-open intervals and midpoint relation at every node.

(defun scta-is-tree-for-p
    (tree array lower upper)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((scta-leaf-shape-p tree)
    (and
     (scta-is-indexes-for-p
      (scta-tree-indexes tree)
      array lower upper)
     (equal upper (+ lower 1))))
   ((scta-node-shape-p tree)
    (let* ((indexes (scta-tree-indexes tree))
           (left (scta-tree-left tree))
           (right (scta-tree-right tree))
           (middle
            (scta-indexes-high
             (scta-tree-indexes left))))
      (and
       (scta-is-indexes-for-p
        indexes array lower upper)
       (equal
        lower
        (scta-indexes-low
         (scta-tree-indexes left)))
       (equal
        upper
        (scta-indexes-high
         (scta-tree-indexes right)))
       (equal
        middle
        (scta-indexes-low
         (scta-tree-indexes right)))
       (< lower middle)
       (< middle upper)
       (equal
        middle
        (scta-midpoint lower upper))
       (scta-is-tree-for-p
        left array lower middle)
       (scta-is-tree-for-p
        right array middle upper))))
   (t nil)))

;; This preserves the universal recursive-call obligation for every source
;; tree satisfying the left-subinterval contract.

(defun-sk scta-all-left-recursive-results-p
    (array lower upper middle)
  (forall (left)
    (implies
     (scta-tree-p left)
     (implies
      (scta-is-tree-for-p
       left array lower middle)
      (and
       (<= 0 (- upper lower))
       (< (- upper middle)
          (- upper lower))
       (<= 0 middle)
       (< middle upper)
       (<= upper (len array)))))))

(defun scta-recursive-branch-obligations-p
    (array lower upper)
  (let ((middle (scta-midpoint lower upper)))
    (and
     (not (equal 2 0))
     (and
      (and
       (and
        (<= 0 (- upper lower))
        (< (- middle lower)
           (- upper lower)))
       (<= 0 lower)
       (< lower middle)
       (<= middle (len array)))
      (scta-all-left-recursive-results-p
       array lower upper middle)))))

(defun scta-construction-obligations-p
    (array lower upper)
  (let ((next (+ lower 1)))
    (if (equal next upper)
        (and
         (<= 0 lower)
         (< lower (len array)))
      (scta-recursive-branch-obligations-p
       array lower upper))))

;; The nested existential witnesses remain internal to the recursive result
;; premise, with the right witness depending on the chosen left subtree.

(defun-sk scta-right-result-witness-p
    (array lower upper middle left result)
  (exists (right)
    (and
     (scta-tree-p right)
     (scta-is-tree-for-p
      right array middle upper)
     (equal
      result
      (scta-node
       (scta-indexes
        lower
        upper
        (+
         (scta-indexes-isum
          (scta-tree-indexes left))
         (scta-indexes-isum
          (scta-tree-indexes right))))
       left
       right)))))

(defun-sk scta-node-result-premise-p
    (array lower upper result)
  (exists (left)
    (and
     (scta-tree-p left)
     (scta-is-tree-for-p
      left
      array
      lower
      (scta-midpoint lower upper))
     (scta-right-result-witness-p
      array
      lower
      upper
      (scta-midpoint lower upper)
      left
      result))))

(defun scta-result-premise-p
    (array lower upper result)
  (if (equal (+ lower 1) upper)
      (equal
       result
       (scta-leaf
        (scta-indexes
         lower
         upper
         (scta-nth-int lower array))))
    (scta-node-result-premise-p
     array lower upper result)))

;; RESULT retains its universal quantifier over the full source tree type.

(defun-sk scta-all-results-correct-p
    (array lower upper)
  (forall (result)
    (implies
     (scta-tree-p result)
     (implies
      (scta-result-premise-p
       array lower upper result)
      (scta-is-tree-for-p
       result array lower upper)))))

;; The arguments encode the source theorem's universally quantified typed
;; parameters. The antecedent is exactly its three bounds assumptions, and
;; the conclusion preserves both generated conjuncts and all inner scopes.

(defun
  ntp4vc-pearl-sumrange-cumulativetree-tree-of-arrayqtvc-statement
  (lower upper array)
  (implies
   (and
    (integerp lower)
    (integerp upper)
    (scta-integer-list-p array)
    (<= 0 lower)
    (< lower upper)
    (<= upper (len array)))
   (and
    (scta-construction-obligations-p
     array lower upper)
    (scta-all-results-correct-p
     array lower upper))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
