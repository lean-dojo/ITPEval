;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/foveoos11_cm/tree_max_TreeMax_maxqtvc: the verification condition
;; for combining subtree maxima into a maximum integer of a nonempty binary
;; tree. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Empty trees are NIL. A node is the exact record
;; (:TREE-MAX-NODE value left right), with an integer value and two recursively
;; encoded trees. This is a bijective encoding of the source's finite
;; inductive binary trees over mathematical integers.

(defun tm-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :tree-max-node)
   (integerp (cadr tree))))

(defun tm-tree-value (tree)
  (cadr tree))

(defun tm-tree-left (tree)
  (caddr tree))

(defun tm-tree-right (tree)
  (cadddr tree))

(defun tm-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (tm-node-shape-p tree)
     (tm-tree-p (tm-tree-left tree))
     (tm-tree-p (tm-tree-right tree)))))

;; Membership and GE-TREE reproduce the two recursive source predicates.
;; GE-TREE CANDIDATE TREE says that every node value is at most CANDIDATE.

(defun tm-member-p (value tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      nil
    (if (tm-node-shape-p tree)
        (or
         (equal (tm-tree-value tree) value)
         (tm-member-p value (tm-tree-left tree))
         (tm-member-p value (tm-tree-right tree)))
      nil)))

(defun tm-ge-tree-p (candidate tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (tm-node-shape-p tree)
        (and
         (<= (tm-tree-value tree) candidate)
         (tm-ge-tree-p candidate (tm-tree-left tree))
         (tm-ge-tree-p candidate (tm-tree-right tree)))
      nil)))

;; This preserves the source match on T: the Null branch is false and every
;; Tree branch is true.

(defun tm-nonnull-match-p (tree)
  (if (equal tree nil)
      nil
    t))

;; O1 remains existentially quantified inside the antecedent for each RESULT.
;; In a node, O1 bounds the right subtree and is selected from the root or
;; right subtree; RESULT bounds the left subtree, dominates O1, and is selected
;; from O1 or the left subtree.

(defun-sk tm-result-premise-p (tree result)
  (exists (o1)
    (and
     (integerp o1)
     (if (equal tree nil)
         nil
       (and
        (tm-ge-tree-p o1 (tm-tree-right tree))
        (<= (tm-tree-value tree) o1)
        (or
         (equal o1 (tm-tree-value tree))
         (tm-member-p o1 (tm-tree-right tree)))
        (tm-ge-tree-p result (tm-tree-left tree))
        (<= o1 result)
        (or
         (equal result o1)
         (tm-member-p result (tm-tree-left tree))))))))

;; RESULT retains its universal quantifier over all mathematical integers.

(defun-sk tm-all-results-correct-p (tree)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (tm-result-premise-p tree result)
      (and
       (tm-ge-tree-p result tree)
       (tm-member-p result tree))))))

(defun-sk
  ntp4vc-pearl-foveoos11-cm-tree-max-treemax-maxqtvc-statement
  ()
  (forall (tree)
    (implies
     (and
      (tm-tree-p tree)
      (not (equal tree nil)))
     (and
      (tm-nonnull-match-p tree)
      (tm-all-results-correct-p tree)))))

(value-triple :itpeval-statement-checked)
:q
