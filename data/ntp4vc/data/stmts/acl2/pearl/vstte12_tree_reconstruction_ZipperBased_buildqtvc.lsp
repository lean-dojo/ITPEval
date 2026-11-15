;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vstte12_tree_reconstruction_ZipperBased_buildqtvc: the initial zipper
;; invariant and the success/failure specification for reconstructing a finite
;; binary tree from its mathematical-integer leaf-depth list. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Finite binary trees are represented bijectively by the exact constructor
;; records (:ZBBQ-LEAF) and (:ZBBQ-NODE left-subtree right-subtree).

(defun zbbq-leaf ()
  (list :zbbq-leaf))

(defun zbbq-node (left right)
  (list :zbbq-node left right))

(defun zbbq-leaf-shape-p (tree)
  (equal tree (zbbq-leaf)))

(defun zbbq-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 3)
   (equal (car tree) :zbbq-node)))

(defun zbbq-tree-left (tree)
  (cadr tree))

(defun zbbq-tree-right (tree)
  (caddr tree))

(defun zbbq-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((zbbq-leaf-shape-p tree)
    t)
   ((zbbq-node-shape-p tree)
    (and
     (zbbq-tree-p (zbbq-tree-left tree))
     (zbbq-tree-p (zbbq-tree-right tree))))
   (t nil)))

(defun zbbq-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (zbbq-integer-list-p (cdr xs)))
    (equal xs nil)))

;; This is the source Tree.depths function.

(defun zbbq-depths (depth tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((zbbq-leaf-shape-p tree)
    (list depth))
   ((zbbq-node-shape-p tree)
    (append
     (zbbq-depths (+ depth 1) (zbbq-tree-left tree))
     (zbbq-depths (+ depth 1) (zbbq-tree-right tree))))
   (t nil)))

;; A forest entry is the exact product record (depth, tree).

(defun zbbq-pair (depth tree)
  (list depth tree))

(defun zbbq-pair-p (pair)
  (and
   (true-listp pair)
   (equal (len pair) 2)
   (integerp (car pair))
   (zbbq-tree-p (cadr pair))))

(defun zbbq-pair-depth (pair)
  (car pair))

(defun zbbq-pair-tree (pair)
  (cadr pair))

(defun zbbq-forest-p (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (consp forest)
      (and
       (zbbq-pair-p (car forest))
       (zbbq-forest-p (cdr forest)))
    (equal forest nil)))

;; The following definitions directly encode forest_depths, greedy, the
;; inductive predicate g, only_leaf, and map_leaf from the source module.

(defun zbbq-forest-depths (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (consp forest)
      (append
       (zbbq-depths
        (zbbq-pair-depth (car forest))
        (zbbq-pair-tree (car forest)))
       (zbbq-forest-depths (cdr forest)))
    nil))

(defun zbbq-greedy-p (depth previous-depth tree)
  (declare (xargs :measure (acl2-count tree)))
  (and
   (not (equal depth previous-depth))
   (cond
    ((zbbq-leaf-shape-p tree)
     t)
    ((zbbq-node-shape-p tree)
     (zbbq-greedy-p
      depth
      (+ previous-depth 1)
      (zbbq-tree-left tree)))
    (t nil))))

(defun zbbq-g-p (forest)
  (declare (xargs :measure (acl2-count forest)))
  (cond
   ((atom forest)
    (equal forest nil))
   ((atom (cdr forest))
    (and
     (equal (cdr forest) nil)
     (zbbq-pair-p (car forest))))
   (t
    (and
     (zbbq-pair-p (car forest))
     (zbbq-pair-p (cadr forest))
     (zbbq-greedy-p
      (zbbq-pair-depth (cadr forest))
      (zbbq-pair-depth (car forest))
      (zbbq-pair-tree (car forest)))
     (zbbq-g-p (cdr forest))))))

(defun zbbq-only-leaf-p (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (consp forest)
      (and
       (zbbq-pair-p (car forest))
       (zbbq-leaf-shape-p (zbbq-pair-tree (car forest)))
       (zbbq-only-leaf-p (cdr forest)))
    (equal forest nil)))

(defun zbbq-map-leaf (depths)
  (declare (xargs :measure (acl2-count depths)))
  (if (consp depths)
      (cons
       (zbbq-pair (car depths) (zbbq-leaf))
       (zbbq-map-leaf (cdr depths)))
    nil))

;; This is the source precondition at the call tc Nil (map_leaf sequence).

(defun zbbq-initial-invariant-p (sequence)
  (let ((o1 (zbbq-map-leaf sequence))
        (o2 nil))
    (and
     (zbbq-g-p o2)
     (if (consp o1)
         (let* ((head (car o1))
                (d2 (zbbq-pair-depth head))
                (tree2 (zbbq-pair-tree head))
                (right-tail (cdr o1)))
           (and
            (zbbq-only-leaf-p right-tail)
            (cond
             ((zbbq-node-shape-p tree2)
              (zbbq-g-p
               (cons
                (zbbq-pair
                 (+ d2 1)
                 (zbbq-tree-left tree2))
                o2)))
             ((zbbq-leaf-shape-p tree2)
              t)
             (t nil))))
       t))))

;; The local expression forest_depths (reverse o2 ++ o1), with o1 and o2
;; bound exactly as in the verification condition.

(defun zbbq-current-forest-depths (sequence)
  (let ((o1 (zbbq-map-leaf sequence))
        (o2 nil))
    (zbbq-forest-depths
     (append (reverse o2) o1))))

;; Every successful result satisfying tc's postcondition reconstructs the
;; original sequence.

(defun-sk zbbq-all-success-results-p (sequence)
  (forall (result)
    (implies
     (zbbq-tree-p result)
     (implies
      (equal
       (zbbq-depths 0 result)
       (zbbq-current-forest-depths sequence))
      (equal
       (zbbq-depths 0 result)
       sequence)))))

;; No finite binary tree has the given root-depth list.

(defun-sk zbbq-no-tree-p (depth-list)
  (forall (tree)
    (implies
     (zbbq-tree-p tree)
     (not
      (equal
       (zbbq-depths 0 tree)
       depth-list)))))

(defun
  ntp4vc-pearl-vstte12-tree-reconstruction-zipperbased-buildqtvc-statement
  (sequence)
  (implies
   (zbbq-integer-list-p sequence)
   (and
    (zbbq-initial-invariant-p sequence)
    (zbbq-all-success-results-p sequence)
    (implies
     (zbbq-no-tree-p
      (zbbq-current-forest-depths sequence))
     (zbbq-no-tree-p sequence)))))

(value-triple :itpeval-statement-checked)
:q
