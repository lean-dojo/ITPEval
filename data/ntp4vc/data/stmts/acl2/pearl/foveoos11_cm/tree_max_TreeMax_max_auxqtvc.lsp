;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/foveoos11_cm/tree_max_TreeMax_max_auxqtvc: the auxiliary
;; verification condition for computing an integer maximum over a binary
;; tree with an accumulator. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Trees are exact finite constructor records:
;; (:TMA-NULL) and (:TMA-TREE integer left-subtree right-subtree).

(defun tma-null-shape-p (tree)
  (equal tree (list :tma-null)))

(defun tma-tree-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :tma-tree)))

(defun tma-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((tma-null-shape-p tree)
    t)
   ((tma-tree-shape-p tree)
    (and
     (integerp (cadr tree))
     (tma-tree-p (caddr tree))
     (tma-tree-p (cadddr tree))))
   (t nil)))

(defun tma-tree-value (tree)
  (cadr tree))

(defun tma-tree-left (tree)
  (caddr tree))

(defun tma-tree-right (tree)
  (cadddr tree))

;; These are the source BinTree.mem and BinTree.ge_tree definitions.

(defun tma-mem-p (value tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((tma-null-shape-p tree)
    nil)
   ((tma-tree-shape-p tree)
    (or
     (equal (tma-tree-value tree) value)
     (tma-mem-p value (tma-tree-left tree))
     (tma-mem-p value (tma-tree-right tree))))
   (t nil)))

(defun tma-ge-tree-p (value tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((tma-null-shape-p tree)
    t)
   ((tma-tree-shape-p tree)
    (and
     (<= (tma-tree-value tree) value)
     (tma-ge-tree-p value (tma-tree-left tree))
     (tma-ge-tree-p value (tma-tree-right tree))))
   (t nil)))

(defun tma-integer-max (left right)
  (if (<= left right)
      right
    left))

;; Preserve the source's repeated matches on the same non-null tree instead
;; of simplifying their constructor equalities.

(defun tma-right-child-case-p (tree)
  (or
   (equal
    (tma-tree-left tree)
    (tma-tree-right tree))
   (equal
    (tma-tree-right tree)
    (tma-tree-right tree))))

(defun tma-left-child-case-p (tree)
  (or
   (equal
    (tma-tree-left tree)
    (tma-tree-left tree))
   (equal
    (tma-tree-right tree)
    (tma-tree-left tree))))

(defun-sk tma-right-continuation-p (tree accumulator-maximum)
  (forall (o2)
    (implies
     (integerp o2)
     (implies
      (and
       (tma-ge-tree-p o2 (tma-tree-right tree))
       (<= accumulator-maximum o2)
       (or
        (equal o2 accumulator-maximum)
        (tma-mem-p o2 (tma-tree-right tree))))
      (tma-left-child-case-p tree)))))

(defun tma-first-conjunct-p (tree accumulator)
  (cond
   ((tma-null-shape-p tree)
    t)
   ((tma-tree-shape-p tree)
    (let ((accumulator-maximum
           (tma-integer-max
            (tma-tree-value tree)
            accumulator)))
      (and
       (tma-right-child-case-p tree)
       (tma-right-continuation-p
        tree accumulator-maximum))))
   (t nil)))

;; The existential witness o2 remains internal to the result premise.

(defun-sk tma-node-result-premise-p (tree accumulator result)
  (exists (o2)
    (and
     (integerp o2)
     (let ((accumulator-maximum
            (tma-integer-max
             (tma-tree-value tree)
             accumulator)))
       (and
        (tma-ge-tree-p o2 (tma-tree-right tree))
        (<= accumulator-maximum o2)
        (or
         (equal o2 accumulator-maximum)
         (tma-mem-p o2 (tma-tree-right tree)))
        (tma-ge-tree-p result (tma-tree-left tree))
        (<= o2 result)
        (or
         (equal result o2)
         (tma-mem-p result (tma-tree-left tree))))))))

(defun tma-result-premise-p (tree accumulator result)
  (cond
   ((tma-null-shape-p tree)
    (equal result accumulator))
   ((tma-tree-shape-p tree)
    (tma-node-result-premise-p
     tree accumulator result))
   (t nil)))

(defun tma-result-conclusion-p (tree accumulator result)
  (and
   (tma-ge-tree-p result tree)
   (<= accumulator result)
   (or
    (equal result accumulator)
    (tma-mem-p result tree))))

(defun-sk tma-all-results-p (tree accumulator)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (tma-result-premise-p
       tree accumulator result)
      (tma-result-conclusion-p
       tree accumulator result)))))

(defun
  ntp4vc-pearl-foveoos11-cm-tree-max-treemax-max-auxqtvc-statement
  (tree accumulator)
  (implies
   (and
    (tma-tree-p tree)
    (integerp accumulator))
   (and
    (tma-first-conjunct-p tree accumulator)
    (tma-all-results-p tree accumulator))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
