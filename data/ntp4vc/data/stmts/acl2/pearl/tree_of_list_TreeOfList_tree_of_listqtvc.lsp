;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/tree_of_list_TreeOfList_tree_of_listqtvc: the full-list binary-tree
;; construction verification condition, preserving inorder traversal and the
;; power-of-two height bounds on nonempty results. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite ACL2 lists represent Why3 lists. Their elements, and all tree
;; labels below, range over ACL2's full object universe, preserving the
;; source's arbitrary polymorphic element type.

(defun tol-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (tol-list-p (cdr xs))
    (equal xs nil)))

;; Empty trees are NIL. Nodes are exact tagged constructor records
;; (:TREE-OF-LIST-NODE left value right).

(defun tol-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :tree-of-list-node)))

(defun tol-tree-left (tree)
  (cadr tree))

(defun tol-tree-value (tree)
  (caddr tree))

(defun tol-tree-right (tree)
  (cadddr tree))

(defun tol-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (tol-node-shape-p tree)
     (tol-tree-p (tol-tree-left tree))
     (tol-tree-p (tol-tree-right tree)))))

(defun tol-tree-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (tol-node-shape-p tree)
        (+
         1
         (tol-tree-size (tol-tree-left tree))
         (tol-tree-size (tol-tree-right tree)))
      0)))

(defun tol-int-max (left right)
  (if (<= left right)
      right
    left))

(defun tol-tree-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (tol-node-shape-p tree)
        (+
         1
         (tol-int-max
          (tol-tree-height (tol-tree-left tree))
          (tol-tree-height (tol-tree-right tree))))
      0)))

(defun tol-tree-inorder (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      nil
    (if (tol-node-shape-p tree)
        (append
         (tol-tree-inorder (tol-tree-left tree))
         (cons
          (tol-tree-value tree)
          (tol-tree-inorder (tol-tree-right tree))))
      nil)))

(defun tol-height-bound-p (tree size)
  (let ((height (tol-tree-height tree)))
    (and
     (<= (expt 2 (- height 1)) size)
     (< size (expt 2 height)))))

;; O2 and O3 retain the source universal quantifiers over every finite binary
;; tree and every finite residual list. The premise is exactly the contract of
;; tree_of_list_aux at O1; the conclusion is the wrapper's two postconditions.

(defun-sk tol-all-aux-results-p (list o1)
  (forall (o2 o3)
    (implies
     (and
      (tol-tree-p o2)
      (tol-list-p o3)
      (equal
       (append (tol-tree-inorder o2) o3)
       list)
      (equal (tol-tree-size o2) o1)
      (implies
       (< 0 o1)
       (tol-height-bound-p o2 o1)))
     (and
      (equal (tol-tree-inorder o2) list)
      (implies
       (< 0 (tol-tree-size o2))
       (tol-height-bound-p
        o2
        (tol-tree-size o2)))))))

;; LIST is the source theorem's universally quantified finite polymorphic
;; list. O1 remains the local binding for its mathematical-integer length.

(defun
  ntp4vc-pearl-tree-of-list-treeoflist-tree-of-listqtvc-statement
  (list)
  (implies
   (tol-list-p list)
   (let ((o1 (len list)))
     (and
      (and
       (<= 0 o1)
       (<= o1 (len list)))
      (tol-all-aux-results-p list o1)))))

(value-triple :itpeval-statement-checked)
:q
