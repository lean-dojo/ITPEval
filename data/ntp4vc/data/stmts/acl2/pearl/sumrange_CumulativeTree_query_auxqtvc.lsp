;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sumrange_CumulativeTree_query_auxqtvc: the cumulative-tree range-query
;; verification condition, preserving the half-open integer sum, recursive-call
;; obligations, and final result relation. This file contains no proof.

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

;; Why3 ComputerDivision.div truncates toward zero. Source-valid interval
;; endpoints are nonnegative, so ACL2 floor division by positive 2 agrees.

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

;; This is the repeated source match asserting that CHILD is an immediate
;; subtree of PARENT.

(defun sct-child-of-p (parent child)
  (and
   (sct-node-shape-p parent)
   (or
    (equal (sct-tree-left parent) child)
    (equal (sct-tree-right parent) child))))

;; Exact precondition generated at each recursive query call.

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

(defun sct-node-false-call-obligations-p
    (tree array lower upper)
  (let* ((left (sct-tree-left tree))
         (right (sct-tree-right tree))
         (middle
          (sct-indexes-high
           (sct-tree-indexes left))))
    (if (<= upper middle)
        (sct-call-context-p
         tree left array lower upper)
      (if (<= middle lower)
          (sct-call-context-p
           tree right array lower upper)
        (and
         (sct-call-context-p
          tree right array middle upper)
         (sct-call-context-p
          tree left array lower middle))))))

;; O1 retains the source universal quantifier over the exact Boolean type and
;; the original nested implication scopes.

(defun-sk sct-all-o1-call-obligations-p
    (tree array lower upper)
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
      (implies
       (not (equal o1 t))
       (sct-node-false-call-obligations-p
        tree array lower upper))))))

(defun sct-node-false-result-relation-p
    (tree array lower upper result)
  (let* ((left (sct-tree-left tree))
         (middle
          (sct-indexes-high
           (sct-tree-indexes left))))
    (if (<= upper middle)
        (equal
         result
         (sct-range-sum array lower upper))
      (if (<= middle lower)
          (equal
           result
           (sct-range-sum array lower upper))
        (equal
         result
         (+
          (sct-range-sum array lower middle)
          (sct-range-sum array middle upper)))))))

(defun sct-node-o1-result-relation-p
    (tree array lower upper result o1)
  (if (equal o1 t)
      (equal
       result
       (sct-indexes-isum
        (sct-tree-indexes tree)))
    (sct-node-false-result-relation-p
     tree array lower upper result)))

;; The existential Boolean is internal to the source body-result relation.

(defun-sk sct-node-body-result-p
    (tree array lower upper result)
  (exists (o1)
    (and
     (booleanp o1)
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
     (sct-node-o1-result-relation-p
      tree array lower upper result o1))))

(defun sct-query-body-result-p
    (tree array lower upper result)
  (if (sct-leaf-shape-p tree)
      (equal
       result
       (sct-indexes-isum
        (sct-tree-indexes tree)))
    (sct-node-body-result-p
     tree array lower upper result)))

;; RESULT retains the source universal quantifier over mathematical integers.

(defun-sk sct-all-results-postcondition-p
    (tree array lower upper)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (sct-query-body-result-p
       tree array lower upper result)
      (equal
       result
       (sct-range-sum array lower upper))))))

(defun
  ntp4vc-pearl-sumrange-cumulativetree-query-auxqtvc-statement
  (tree array lower upper)
  (implies
   (and
    (sct-tree-p tree)
    (sct-integer-list-p array)
    (integerp lower)
    (integerp upper)
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
   (and
    (if (sct-leaf-shape-p tree)
        t
      (sct-all-o1-call-obligations-p
       tree array lower upper))
    (sct-all-results-postcondition-p
     tree array lower upper))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
