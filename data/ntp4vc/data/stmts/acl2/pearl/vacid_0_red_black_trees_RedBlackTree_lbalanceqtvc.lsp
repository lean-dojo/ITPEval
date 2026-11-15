;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vacid_0_red_black_trees_RedBlackTree_lbalanceqtvc: the left-balancing
;; verification condition for integer-keyed red-black search trees, preserving
;; the BST invariant, black height, and key/value membership. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Colors and trees are exact tagged constructor records for the Why3
;; datatypes. Keys and values retain their source domain of mathematical
;; integers.

(defun rbt-color-p (color)
  (or
   (equal color :rbt-red)
   (equal color :rbt-black)))

(defun rbt-leaf ()
  :rbt-leaf)

(defun rbt-node (color left key value right)
  (cons
   :rbt-node
   (cons
    color
    (cons
     left
     (cons key (cons value right))))))

(defun rbt-leaf-shape-p (tree)
  (equal tree :rbt-leaf))

(defun rbt-node-shape-p (tree)
  (and
   (consp tree)
   (equal (car tree) :rbt-node)
   (consp (cdr tree))
   (consp (cddr tree))
   (consp (cdddr tree))
   (consp (cddddr tree))))

(defun rbt-node-color (tree)
  (cadr tree))

(defun rbt-node-left (tree)
  (caddr tree))

(defun rbt-node-key (tree)
  (cadddr tree))

(defun rbt-node-value (tree)
  (car (cddddr tree)))

(defun rbt-node-right (tree)
  (cdr (cddddr tree)))

(defun rbt-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((rbt-leaf-shape-p tree)
    t)
   ((rbt-node-shape-p tree)
    (and
     (rbt-color-p (rbt-node-color tree))
     (rbt-tree-p (rbt-node-left tree))
     (integerp (rbt-node-key tree))
     (integerp (rbt-node-value tree))
     (rbt-tree-p (rbt-node-right tree))))
   (t nil)))

;; Occurrence, ordering, and the binary-search-tree invariant are direct
;; recursive renderings of the source predicates.

(defun rbt-memt-p (tree key value)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((rbt-leaf-shape-p tree)
    nil)
   ((rbt-node-shape-p tree)
    (or
     (and
      (equal key (rbt-node-key tree))
      (equal value (rbt-node-value tree)))
     (rbt-memt-p (rbt-node-left tree) key value)
     (rbt-memt-p (rbt-node-right tree) key value)))
   (t nil)))

(defun-sk rbt-lt-tree-p (bound tree)
  (forall (key value)
    (implies
     (and
      (integerp key)
      (integerp value))
     (implies
      (rbt-memt-p tree key value)
      (< key bound)))))

(defun-sk rbt-gt-tree-p (bound tree)
  (forall (key value)
    (implies
     (and
      (integerp key)
      (integerp value))
     (implies
      (rbt-memt-p tree key value)
      (< bound key)))))

(defun rbt-bst-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((rbt-leaf-shape-p tree)
    t)
   ((rbt-node-shape-p tree)
    (let ((left (rbt-node-left tree))
          (key (rbt-node-key tree))
          (right (rbt-node-right tree)))
      (and
       (rbt-bst-p left)
       (rbt-bst-p right)
       (rbt-lt-tree-p key left)
       (rbt-gt-tree-p key right))))
   (t nil)))

;; These definitions preserve the source red-black and almost-red-black
;; predicates, including their integer black-height parameter.

(defun rbt-is-not-red-p (tree)
  (cond
   ((rbt-leaf-shape-p tree)
    t)
   ((and
     (rbt-node-shape-p tree)
     (equal (rbt-node-color tree) :rbt-red))
    nil)
   ((and
     (rbt-node-shape-p tree)
     (equal (rbt-node-color tree) :rbt-black))
    t)
   (t nil)))

(defun rbt-rbtree-p (height tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((rbt-leaf-shape-p tree)
    (equal height 0))
   ((and
     (rbt-node-shape-p tree)
     (equal (rbt-node-color tree) :rbt-red))
    (let ((left (rbt-node-left tree))
          (right (rbt-node-right tree)))
      (and
       (rbt-rbtree-p height left)
       (rbt-rbtree-p height right)
       (rbt-is-not-red-p left)
       (rbt-is-not-red-p right))))
   ((and
     (rbt-node-shape-p tree)
     (equal (rbt-node-color tree) :rbt-black))
    (and
     (rbt-rbtree-p
      (- height 1)
      (rbt-node-left tree))
     (rbt-rbtree-p
      (- height 1)
      (rbt-node-right tree))))
   (t nil)))

(defun rbt-almost-rbtree-p (height tree)
  (cond
   ((rbt-leaf-shape-p tree)
    (equal height 0))
   ((and
     (rbt-node-shape-p tree)
     (equal (rbt-node-color tree) :rbt-red))
    (and
     (rbt-rbtree-p
      height
      (rbt-node-left tree))
     (rbt-rbtree-p
      height
      (rbt-node-right tree))))
   ((and
     (rbt-node-shape-p tree)
     (equal (rbt-node-color tree) :rbt-black))
    (and
     (rbt-rbtree-p
      (- height 1)
      (rbt-node-left tree))
     (rbt-rbtree-p
      (- height 1)
      (rbt-node-right tree))))
   (t nil)))

(defun rbt-red-node-p (tree)
  (and
   (rbt-node-shape-p tree)
   (equal (rbt-node-color tree) :rbt-red)))

;; The first red-red pattern has source match precedence when both children of
;; the red root are red.

(defun rbt-lbalance-result (left key value right)
  (cond
   ((and
     (rbt-red-node-p left)
     (rbt-red-node-p (rbt-node-left left)))
    (let ((red-left (rbt-node-left left)))
      (rbt-node
       :rbt-red
       (rbt-node
        :rbt-black
        (rbt-node-left red-left)
        (rbt-node-key red-left)
        (rbt-node-value red-left)
        (rbt-node-right red-left))
       (rbt-node-key left)
       (rbt-node-value left)
       (rbt-node
        :rbt-black
        (rbt-node-right left)
        key
        value
        right))))
   ((and
     (rbt-red-node-p left)
     (rbt-red-node-p (rbt-node-right left)))
    (let ((red-right (rbt-node-right left)))
      (rbt-node
       :rbt-red
       (rbt-node
        :rbt-black
        (rbt-node-left left)
        (rbt-node-key left)
        (rbt-node-value left)
        (rbt-node-left red-right))
       (rbt-node-key red-right)
       (rbt-node-value red-right)
       (rbt-node
        :rbt-black
        (rbt-node-right red-right)
        key
        value
        right))))
   (t
    (rbt-node
     :rbt-black left key value right))))

;; The exported VC contains a separate pattern-match conjunct whose every
;; branch is true.

(defun rbt-lbalance-match-safety-p (left)
  (cond
   ((and
     (rbt-red-node-p left)
     (rbt-red-node-p (rbt-node-left left)))
    t)
   ((and
     (rbt-red-node-p left)
     (rbt-red-node-p (rbt-node-right left)))
    t)
   (t t)))

(defun-sk rbt-lbalance-height-post-p
    (left right result)
  (forall (height)
    (implies
     (integerp height)
     (implies
      (and
       (rbt-almost-rbtree-p height left)
       (rbt-rbtree-p height right))
      (rbt-rbtree-p (+ height 1) result)))))

(defun-sk rbt-lbalance-membership-post-p
    (key left right value result)
  (forall (other-key other-value)
    (implies
     (and
      (integerp other-key)
      (integerp other-value))
     (equal
      (rbt-memt-p result other-key other-value)
      (if (equal other-key key)
          (equal other-value value)
        (or
         (rbt-memt-p left other-key other-value)
         (rbt-memt-p right other-key other-value)))))))

;; RESULT remains universally quantified over the exact tree carrier, and the
;; body relation is equality with the deterministic source match.

(defun-sk rbt-lbalance-all-results-p
    (key left right value)
  (forall (result)
    (implies
     (rbt-tree-p result)
     (implies
      (equal
       result
       (rbt-lbalance-result
        left key value right))
      (and
       (rbt-bst-p result)
       (rbt-lbalance-height-post-p
        left right result)
       (rbt-lbalance-membership-post-p
        key left right value result))))))

(defun
  ntp4vc-pearl-vacid-0-red-black-trees-redblacktree-lbalanceqtvc-statement
  (key left right value)
  (implies
   (and
    (integerp key)
    (rbt-tree-p left)
    (rbt-tree-p right)
    (integerp value)
    (rbt-lt-tree-p key left)
    (rbt-gt-tree-p key right)
    (rbt-bst-p left)
    (rbt-bst-p right))
   (and
    (rbt-lbalance-match-safety-p left)
    (rbt-lbalance-all-results-p
     key left right value))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
