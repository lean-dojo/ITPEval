;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/braun_trees_BraunHeaps_fast_sizeqtvc: the fast-size verification
;; condition for Braun-balanced binary trees, including the subtree balance
;; bounds and the universally quantified integer result equation.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Empty trees are NIL. Nodes are exact records
;; (:BRAUN-NODE left element right). The element field ranges over ACL2's
;; full object universe because this verification condition depends only on
;; tree shape, preserving the source's arbitrary element labels.

(defun bfs-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :braun-node)))

(defun bfs-tree-left (tree)
  (cadr tree))

(defun bfs-tree-right (tree)
  (cadddr tree))

(defun bfs-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (bfs-node-shape-p tree)
     (bfs-tree-p (bfs-tree-left tree))
     (bfs-tree-p (bfs-tree-right tree)))))

(defun bfs-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (bfs-node-shape-p tree)
        (+
         1
         (bfs-size (bfs-tree-left tree))
         (bfs-size (bfs-tree-right tree)))
      0)))

(defun bfs-inv-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (bfs-node-shape-p tree)
        (let ((left (bfs-tree-left tree))
              (right (bfs-tree-right tree)))
          (and
           (or
            (equal (bfs-size left)
                   (bfs-size right))
            (equal (bfs-size left)
                   (+ (bfs-size right) 1)))
           (bfs-inv-p left)
           (bfs-inv-p right)))
      nil)))

;; This is the theorem's first match expression. In the node branch, the
;; repeated match on the original tree yields exactly LEFT = RIGHT or
;; RIGHT = RIGHT, followed by the right invariant and the left/right size
;; bounds.

(defun bfs-structural-conclusion-p (tree)
  (if (equal tree nil)
      t
    (let ((left (bfs-tree-left tree))
          (right (bfs-tree-right tree)))
      (and
       (or
        (equal left right)
        (equal right right))
       (bfs-inv-p right)
       (bfs-inv-p left)
       (<= 0 (bfs-size right))
       (<= (bfs-size right)
           (bfs-size left))
       (<= (bfs-size left)
           (+ (bfs-size right) 1))))))

;; The source offset O1 remains existentially quantified over all
;; mathematical integers inside the node-result premise.

(defun-sk bfs-node-result-premise-p (left right result)
  (exists (o1)
    (and
     (integerp o1)
     (equal
      (bfs-size left)
      (+ (bfs-size right) o1))
     (equal
      result
      (+
       1
       (* 2 (bfs-size right))
       o1)))))

(defun bfs-result-premise-p (tree result)
  (if (equal tree nil)
      (equal result 0)
    (bfs-node-result-premise-p
     (bfs-tree-left tree)
     (bfs-tree-right tree)
     result)))

;; RESULT retains its source universal quantifier over mathematical integers.

(defun-sk bfs-all-results-p (tree)
  (forall (result)
    (implies
     (and
      (integerp result)
      (bfs-result-premise-p tree result))
     (equal result (bfs-size tree)))))

(defun-sk
  ntp4vc-pearl-braun-trees-braunheaps-fast-sizeqtvc-statement
  ()
  (forall (tree)
    (implies
     (and
      (bfs-tree-p tree)
      (bfs-inv-p tree))
     (and
      (bfs-structural-conclusion-p tree)
      (bfs-all-results-p tree)))))

(value-triple :itpeval-statement-checked)
:q
