;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vstte12_tree_reconstruction_TreeReconstruction_buildqtvc: the tree
;; reconstruction wrapper verification condition over mathematical-integer
;; leaf-depth lists, covering successful prefix results and reconstruction
;; failure. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Finite binary trees are represented bijectively by the exact constructor
;; records (:TRBQ-LEAF) and (:TRBQ-NODE left-subtree right-subtree).

(defun trbq-leaf ()
  (list :trbq-leaf))

(defun trbq-node (left right)
  (list :trbq-node left right))

(defun trbq-leaf-shape-p (tree)
  (equal tree (trbq-leaf)))

(defun trbq-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 3)
   (equal (car tree) :trbq-node)))

(defun trbq-tree-left (tree)
  (cadr tree))

(defun trbq-tree-right (tree)
  (caddr tree))

(defun trbq-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((trbq-leaf-shape-p tree)
    t)
   ((trbq-node-shape-p tree)
    (and
     (trbq-tree-p (trbq-tree-left tree))
     (trbq-tree-p (trbq-tree-right tree))))
   (t nil)))

(defun trbq-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (trbq-integer-list-p (cdr xs)))
    (equal xs nil)))

;; This is the source Tree.depths function. A leaf contributes the current
;; integer depth, while a node concatenates the two child depth lists after
;; increasing the depth by one.

(defun trbq-depths (depth tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((trbq-leaf-shape-p tree)
    (list depth))
   ((trbq-node-shape-p tree)
    (append
     (trbq-depths (+ depth 1) (trbq-tree-left tree))
     (trbq-depths (+ depth 1) (trbq-tree-right tree))))
   (t nil)))

;; No finite binary tree has SEQUENCE as its depth list at root depth zero.

(defun-sk trbq-no-exact-tree-p (sequence)
  (forall (tree)
    (implies
     (trbq-tree-p tree)
     (not
      (equal
       (trbq-depths 0 tree)
       sequence)))))

;; No finite binary tree has a depth list that is a prefix of SEQUENCE.

(defun-sk trbq-no-prefix-tree-p (sequence)
  (forall (tree suffix)
    (implies
     (and
      (trbq-tree-p tree)
      (trbq-integer-list-p suffix))
     (not
      (equal
       (append (trbq-depths 0 tree) suffix)
       sequence)))))

;; For every successful build_rec result, an empty remainder gives an exact
;; reconstruction, while a nonempty remainder makes exact reconstruction by
;; any finite binary tree impossible.

(defun-sk trbq-all-success-results-p (sequence)
  (forall (tree suffix)
    (implies
     (and
      (trbq-tree-p tree)
      (trbq-integer-list-p suffix))
     (implies
      (equal
       sequence
       (append (trbq-depths 0 tree) suffix))
      (if (equal suffix nil)
          (equal (trbq-depths 0 tree) sequence)
        (trbq-no-exact-tree-p sequence))))))

(defun
  ntp4vc-pearl-vstte12-tree-reconstruction-treereconstruction-buildqtvc-statement
  (sequence)
  (implies
   (trbq-integer-list-p sequence)
   (and
    (trbq-all-success-results-p sequence)
    (implies
     (trbq-no-prefix-tree-p sequence)
     (trbq-no-exact-tree-p sequence)))))

(value-triple :itpeval-statement-checked)
:q
