;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/leftist_heap_LeftistHeap_is_emptyqtvc: the leftist-heap emptiness
;; verification condition, equating the returned Boolean with the tree's
;; recursively computed size being zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Empty trees are NIL. Nodes are exact records
;; (:LEFTIST-IS-EMPTY-NODE rank left element right), preserving the source's
;; finite inductive tree domain, integer rank annotation, and arbitrary
;; element labels.

(defun lhie-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 5)
   (equal (car tree) :leftist-is-empty-node)))

(defun lhie-tree-rank-field (tree)
  (cadr tree))

(defun lhie-tree-left (tree)
  (caddr tree))

(defun lhie-tree-right (tree)
  (car (cddddr tree)))

(defun lhie-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (lhie-node-shape-p tree)
     (integerp (lhie-tree-rank-field tree))
     (lhie-tree-p (lhie-tree-left tree))
     (lhie-tree-p (lhie-tree-right tree)))))

(defun lhie-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (lhie-node-shape-p tree)
        (+
         1
         (lhie-size (lhie-tree-left tree))
         (lhie-size (lhie-tree-right tree)))
      0)))

;; This is the source match assumption: the result is true exactly in the
;; empty-tree branch and false in every node branch.

(defun lhie-branch-result-p (tree result)
  (if (equal tree nil)
      (equal result t)
    (equal result nil)))

(defun-sk
  ntp4vc-pearl-leftist-heap-leftistheap-is-emptyqtvc-statement
  ()
  (forall (tree result)
    (implies
     (and
      (lhie-tree-p tree)
      (booleanp result)
      (lhie-branch-result-p tree result))
     (iff
      (equal result t)
      (equal (lhie-size tree) 0)))))

(value-triple :itpeval-statement-checked)
:q
