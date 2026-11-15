;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vstte12_tree_reconstruction_Harness_harness2qtvc: no finite binary
;; tree has left-to-right leaf depths 1, 3, 2, 2 when its root is at depth
;; zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Trees are represented bijectively by the exact finite constructor records
;; (:H2-LEAF) and (:H2-NODE left-subtree right-subtree).

(defun h2-leaf-shape-p (tree)
  (equal tree (list :h2-leaf)))

(defun h2-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 3)
   (equal (car tree) :h2-node)))

(defun h2-tree-left (tree)
  (cadr tree))

(defun h2-tree-right (tree)
  (caddr tree))

(defun h2-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((h2-leaf-shape-p tree)
    t)
   ((h2-node-shape-p tree)
    (and
     (h2-tree-p (h2-tree-left tree))
     (h2-tree-p (h2-tree-right tree))))
   (t nil)))

;; This is the source Tree.depths function: leaves contribute their current
;; mathematical-integer depth, and nodes concatenate the left and right
;; leaf-depth lists after increasing the depth by one.

(defun h2-depths (depth tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((h2-leaf-shape-p tree)
    (list depth))
   ((h2-node-shape-p tree)
    (append
     (h2-depths (+ depth 1) (h2-tree-left tree))
     (h2-depths (+ depth 1) (h2-tree-right tree))))
   (t nil)))

;; TREE is the source theorem's universally quantified finite binary tree.

(defun
  ntp4vc-pearl-vstte12-tree-reconstruction-harness-harness2qtvc-statement
  (tree)
  (implies
   (h2-tree-p tree)
   (not
    (equal
     (h2-depths 0 tree)
     (list 1 3 2 2)))))

(value-triple :itpeval-statement-checked)
:q
