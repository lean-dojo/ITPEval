;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sumrange_CumulativeTree_query_aux_complexityqtvc: the cumulative-tree
;; range-query verification condition, preserving the half-open integer sum,
;; recursive branch obligations, and depth-based credit bound. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Proper finite integer lists represent Why3 arrays of mathematical integers.

(defun sct-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (sct-integer-list-p (cdr xs)))
    (equal xs nil)))

(defun sct-nth-int (index xs)
  (let ((value (nth (nfix index) xs)))
    (if (integerp value)
        value
      0)))

;; On source-valid bounds this is exactly ArraySum.sum over [LOWER, UPPER).

(defun sct-range-sum (xs lower upper)
  (declare
   (xargs :measure
          (nfix (- upper lower))))
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (+
       (sct-nth-int (- upper 1) xs)
       (sct-range-sum xs lower (- upper 1)))
    0))

;; INDEXES and TREE are exact constructor records for the source datatypes.

(defun sct-indexes (low high isum)
  (list :sct-indexes low high isum))

(defun sct-indexes-shape-p (indexes)
  (and
   (true-listp indexes)
   (equal (len indexes) 4)
   (equal (car indexes) :sct-indexes)))

(defun sct-indexes-p (indexes)
  (and
   (sct-indexes-shape-p indexes)
   (integerp (cadr indexes))
   (integerp (caddr indexes))
   (integerp (cadddr indexes))))

(defun sct-indexes-low (indexes)
  (cadr indexes))

(defun sct-indexes-high (indexes)
  (caddr indexes))

(defun sct-indexes-isum (indexes)
  (cadddr indexes))

(defun sct-leaf (indexes)
  (list :sct-leaf indexes))

(defun sct-node (indexes left right)
  (list :sct-node indexes left right))

(defun sct-leaf-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 2)
   (equal (car tree) :sct-leaf)))

(defun sct-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :sct-node)))

(defun sct-tree-indexes (tree)
  (cadr tree))

(defun sct-tree-left (tree)
  (caddr tree))

(defun sct-tree-right (tree)
  (cadddr tree))

(defun sct-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((sct-leaf-shape-p tree)
    (sct-indexes-p (sct-tree-indexes tree)))
   ((sct-node-shape-p tree)
    (and
     (sct-indexes-p (sct-tree-indexes tree))
     (sct-tree-p (sct-tree-left tree))
     (sct-tree-p (sct-tree-right tree))))
   (t nil)))

;; Why3 ComputerDivision.div is Euclidean division. Its numerator is
;; nonnegative in every source-valid tree interval, so ACL2 floor division by
;; the positive divisor 2 is the same integer midpoint.

(defun sct-midpoint (lower upper)
  (floor (+ lower upper) 2))

(defun sct-is-indexes-for-p
    (indexes array lower upper)
  (and
   (sct-indexes-p indexes)
   (sct-integer-list-p array)
   (integerp lower)
   (integerp upper)
   (equal (sct-indexes-low indexes) lower)
   (equal (sct-indexes-high indexes) upper)
   (<= 0 lower)
   (< lower upper)
   (<= upper (len array))
   (equal
    (sct-indexes-isum indexes)
    (sct-range-sum array lower upper))))

(defun sct-is-tree-for-p
    (tree array lower upper)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((sct-leaf-shape-p tree)
    (and
     (sct-is-indexes-for-p
      (sct-tree-indexes tree)
      array lower upper)
     (equal upper (+ lower 1))))
   ((sct-node-shape-p tree)
    (let* ((indexes (sct-tree-indexes tree))
           (left (sct-tree-left tree))
           (right (sct-tree-right tree))
           (middle
            (sct-indexes-high
             (sct-tree-indexes left))))
      (and
       (sct-is-indexes-for-p
        indexes array lower upper)
       (equal
        lower
        (sct-indexes-low
         (sct-tree-indexes left)))
       (equal
        upper
        (sct-indexes-high
         (sct-tree-indexes right)))
       (equal
        middle
        (sct-indexes-low
         (sct-tree-indexes right)))
       (< lower middle)
       (< middle upper)
       (equal
        middle
        (sct-midpoint lower upper))
       (sct-is-tree-for-p
        left array lower middle)
       (sct-is-tree-for-p
        right array middle upper))))
   (t nil)))

(defun sct-depth (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((sct-leaf-shape-p tree)
    1)
   ((sct-node-shape-p tree)
    (+
     1
     (max
      (sct-depth (sct-tree-left tree))
      (sct-depth (sct-tree-right tree)))))
   (t 0)))

(defun sct-cost-bound (tree lower upper)
  (let ((root (sct-tree-indexes tree)))
    (if (and
         (equal lower (sct-indexes-low root))
         (equal upper (sct-indexes-high root)))
        1
      (if (or
           (equal lower (sct-indexes-low root))
           (equal upper (sct-indexes-high root)))
          (* 2 (sct-depth tree))
        (* 4 (sct-depth tree))))))

;; This is the repeated source match proving that CHILD is one of PARENT's
;; immediate subtrees.

(defun sct-child-of-p (parent child)
  (and
   (sct-node-shape-p parent)
   (or
    (equal (sct-tree-left parent) child)
    (equal (sct-tree-right parent) child))))

;; Exact recursive-call context generated for a child interval.

(defun sct-call-context-p
    (parent child array lower upper)
  (let ((child-root (sct-tree-indexes child)))
    (and
     (sct-child-of-p parent child)
     (sct-is-tree-for-p
      child
      array
      (sct-indexes-low child-root)
      (sct-indexes-high child-root))
     (<= 0 (sct-indexes-low child-root))
     (<= (sct-indexes-low child-root) lower)
     (< lower upper)
     (<= upper (sct-indexes-high child-root))
     (<= (sct-indexes-high child-root)
         (len array)))))

;; Continuation after one recursive query call, retaining the universal
;; mathematical-integer credit result.

(defun-sk sct-single-call-continuation-p
    (parent child parent-lower parent-upper
            child-lower child-upper initial-credit)
  (forall (next-credit)
    (implies
     (integerp next-credit)
     (implies
      (<=
       (- next-credit (+ initial-credit 1))
       (sct-cost-bound
        child child-lower child-upper))
      (<=
       (- next-credit initial-credit)
       (sct-cost-bound
        parent parent-lower parent-upper))))))

;; Final continuation after the second recursive call in the split case.

(defun-sk sct-all-second-credits-p
    (parent left array lower upper initial-credit
            middle first-credit)
  (forall (second-credit)
    (implies
     (integerp second-credit)
     (implies
      (<=
       (- second-credit first-credit)
       (sct-cost-bound left lower middle))
      (and
       (<=
        (- second-credit initial-credit)
        (sct-cost-bound parent lower upper))
       (equal
        (+
         (sct-range-sum array lower middle)
         (sct-range-sum array middle upper))
        (sct-range-sum array lower upper)))))))

;; Continuation after the right recursive call and before the left recursive
;; call in the split case.

(defun-sk sct-all-first-credits-p
    (parent left right array lower upper initial-credit middle)
  (forall (first-credit)
    (implies
     (integerp first-credit)
     (implies
      (<=
       (- first-credit (+ initial-credit 1))
       (sct-cost-bound right middle upper))
      (and
       (sct-call-context-p
        parent left array lower middle)
       (sct-all-second-credits-p
        parent left array lower upper initial-credit
        middle first-credit))))))

(defun sct-left-only-branch-p
    (parent left array lower upper initial-credit)
  (and
   (sct-call-context-p
    parent left array lower upper)
   (sct-single-call-continuation-p
    parent left lower upper lower upper initial-credit)))

(defun sct-right-only-branch-p
    (parent right array lower upper initial-credit)
  (and
   (sct-call-context-p
    parent right array lower upper)
   (sct-single-call-continuation-p
    parent right lower upper lower upper initial-credit)))

(defun sct-split-branch-p
    (parent left right array lower upper initial-credit middle)
  (and
   (sct-call-context-p
    parent right array middle upper)
   (sct-all-first-credits-p
    parent left right array lower upper initial-credit middle)))

(defun sct-leaf-conclusion-p
    (tree array lower upper initial-credit)
  (and
   (<=
    (- (+ initial-credit 1) initial-credit)
    (sct-cost-bound tree lower upper))
   (equal
    (sct-indexes-isum
     (sct-tree-indexes tree))
    (sct-range-sum array lower upper))))

(defun sct-node-false-branch-p
    (tree array lower upper initial-credit)
  (let* ((left (sct-tree-left tree))
         (right (sct-tree-right tree))
         (middle
          (sct-indexes-high
           (sct-tree-indexes left))))
    (if (<= upper middle)
        (sct-left-only-branch-p
         tree left array lower upper initial-credit)
      (if (<= middle lower)
          (sct-right-only-branch-p
           tree right array lower upper initial-credit)
        (sct-split-branch-p
         tree left right array lower upper initial-credit middle)))))

(defun sct-node-o1-conclusion-p
    (tree array lower upper initial-credit o1)
  (if (equal o1 t)
      (sct-leaf-conclusion-p
       tree array lower upper initial-credit)
    (sct-node-false-branch-p
     tree array lower upper initial-credit)))

;; O1 retains the source quantifier over the exact two-element Boolean type.

(defun-sk sct-all-o1-p
    (tree array lower upper initial-credit)
  (forall (o1)
    (implies
     (booleanp o1)
     (implies
      (equal
       o1
       (if
        (equal
         lower
         (sct-indexes-low
          (sct-tree-indexes tree)))
        (if
         (equal
          upper
          (sct-indexes-high
           (sct-tree-indexes tree)))
         t
         nil)
        nil))
      (sct-node-o1-conclusion-p
       tree array lower upper initial-credit o1)))))

(defun
  ntp4vc-pearl-sumrange-cumulativetree-query-aux-complexityqtvc-statement
  (tree array lower upper initial-credit)
  (implies
   (and
    (sct-tree-p tree)
    (sct-integer-list-p array)
    (integerp lower)
    (integerp upper)
    (integerp initial-credit)
    (sct-is-tree-for-p
     tree
     array
     (sct-indexes-low
      (sct-tree-indexes tree))
     (sct-indexes-high
      (sct-tree-indexes tree)))
    (<=
     0
     (sct-indexes-low
      (sct-tree-indexes tree)))
    (<=
     (sct-indexes-low
      (sct-tree-indexes tree))
     lower)
    (< lower upper)
    (<=
     upper
     (sct-indexes-high
      (sct-tree-indexes tree)))
    (<=
     (sct-indexes-high
      (sct-tree-indexes tree))
     (len array)))
   (if (sct-leaf-shape-p tree)
       (sct-leaf-conclusion-p
        tree array lower upper initial-credit)
     (sct-all-o1-p
      tree array lower upper initial-credit))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
