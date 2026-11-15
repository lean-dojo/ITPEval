;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vstte12_tree_reconstruction_Harness_harnessqtvc: the leaf-depth list
;; 1, 3, 3, 2 uniquely reconstructs the specified finite binary tree when
;; its root is at depth zero, and such a tree exists. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Trees are represented bijectively by the exact finite constructor records
;; (:H1-LEAF) and (:H1-NODE left-subtree right-subtree).

(defun h1-leaf ()
  (list :h1-leaf))

(defun h1-node (left right)
  (list :h1-node left right))

(defun h1-leaf-shape-p (tree)
  (equal tree (h1-leaf)))

(defun h1-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 3)
   (equal (car tree) :h1-node)))

(defun h1-tree-left (tree)
  (cadr tree))

(defun h1-tree-right (tree)
  (caddr tree))

(defun h1-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((h1-leaf-shape-p tree)
    t)
   ((h1-node-shape-p tree)
    (and
     (h1-tree-p (h1-tree-left tree))
     (h1-tree-p (h1-tree-right tree))))
   (t nil)))

;; This is the source Tree.depths function: leaves contribute their current
;; mathematical-integer depth, and nodes concatenate the left and right
;; leaf-depth lists after increasing the depth by one.

(defun h1-depths (depth tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((h1-leaf-shape-p tree)
    (list depth))
   ((h1-node-shape-p tree)
    (append
     (h1-depths (+ depth 1) (h1-tree-left tree))
     (h1-depths (+ depth 1) (h1-tree-right tree))))
   (t nil)))

(defun h1-expected-tree ()
  (h1-node
   (h1-leaf)
   (h1-node
    (h1-node (h1-leaf) (h1-leaf))
    (h1-leaf))))

;; This is the source universal conjunct: every finite binary tree with the
;; required leaf depths is the specified reconstruction.

(defun-sk h1-unique-reconstruction-p ()
  (forall (result)
    (implies
     (h1-tree-p result)
     (implies
      (equal
       (h1-depths 0 result)
       (list 1 3 3 2))
      (equal result (h1-expected-tree))))))

;; This is the universally quantified nonexistence claim negated by the
;; source statement's second conjunct.

(defun-sk h1-no-reconstruction-p ()
  (forall (tree)
    (implies
     (h1-tree-p tree)
     (not
      (equal
       (h1-depths 0 tree)
       (list 1 3 3 2))))))

(defun
  ntp4vc-pearl-vstte12-tree-reconstruction-harness-harnessqtvc-statement
  ()
  (and
   (h1-unique-reconstruction-p)
   (not (h1-no-reconstruction-p))))

(value-triple :itpeval-statement-checked)
:q
