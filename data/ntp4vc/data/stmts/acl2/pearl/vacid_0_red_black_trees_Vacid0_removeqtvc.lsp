;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vacid_0_red_black_trees_Vacid0_removeqtvc: the remove verification
;; condition for an integer-keyed red-black tree map with a default value,
;; preserving its invariant and quantified membership postcondition. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Colors and trees are exact tagged constructor records for the Why3
;; datatypes. Keys, values, defaults, and black heights retain their
;; mathematical integer domains.

(defun v0r-color-p (color)
  (or
   (equal color :v0r-red)
   (equal color :v0r-black)))

(defun v0r-leaf ()
  :v0r-leaf)

(defun v0r-node (color left key value right)
  (cons
   :v0r-node
   (cons
    color
    (cons
     left
     (cons key (cons value right))))))

(defun v0r-leaf-shape-p (tree)
  (equal tree :v0r-leaf))

(defun v0r-node-shape-p (tree)
  (and
   (consp tree)
   (equal (car tree) :v0r-node)
   (consp (cdr tree))
   (consp (cddr tree))
   (consp (cdddr tree))
   (consp (cddddr tree))))

(defun v0r-node-color (tree)
  (cadr tree))

(defun v0r-node-left (tree)
  (caddr tree))

(defun v0r-node-key (tree)
  (cadddr tree))

(defun v0r-node-value (tree)
  (car (cddddr tree)))

(defun v0r-node-right (tree)
  (cdr (cddddr tree)))

(defun v0r-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((v0r-leaf-shape-p tree)
    t)
   ((v0r-node-shape-p tree)
    (and
     (v0r-color-p (v0r-node-color tree))
     (v0r-tree-p (v0r-node-left tree))
     (integerp (v0r-node-key tree))
     (integerp (v0r-node-value tree))
     (v0r-tree-p (v0r-node-right tree))))
   (t nil)))

;; Occurrence, ordering, and the binary-search-tree invariant are direct
;; recursive renderings of the source predicates.

(defun v0r-memt-p (tree key value)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((v0r-leaf-shape-p tree)
    nil)
   ((v0r-node-shape-p tree)
    (or
     (and
      (equal key (v0r-node-key tree))
      (equal value (v0r-node-value tree)))
     (v0r-memt-p (v0r-node-left tree) key value)
     (v0r-memt-p (v0r-node-right tree) key value)))
   (t nil)))

(defun-sk v0r-lt-tree-p (bound tree)
  (forall (key value)
    (implies
     (and
      (integerp key)
      (integerp value))
     (implies
      (v0r-memt-p tree key value)
      (< key bound)))))

(defun-sk v0r-gt-tree-p (bound tree)
  (forall (key value)
    (implies
     (and
      (integerp key)
      (integerp value))
     (implies
      (v0r-memt-p tree key value)
      (< bound key)))))

(defun v0r-bst-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((v0r-leaf-shape-p tree)
    t)
   ((v0r-node-shape-p tree)
    (let ((left (v0r-node-left tree))
          (key (v0r-node-key tree))
          (right (v0r-node-right tree)))
      (and
       (v0r-bst-p left)
       (v0r-bst-p right)
       (v0r-lt-tree-p key left)
       (v0r-gt-tree-p key right))))
   (t nil)))

;; The red-black predicate preserves the source integer black-height
;; parameter and the requirement that a red node has no red child.

(defun v0r-is-not-red-p (tree)
  (cond
   ((v0r-leaf-shape-p tree)
    t)
   ((and
     (v0r-node-shape-p tree)
     (equal (v0r-node-color tree) :v0r-red))
    nil)
   ((and
     (v0r-node-shape-p tree)
     (equal (v0r-node-color tree) :v0r-black))
    t)
   (t nil)))

(defun v0r-rbtree-p (height tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((v0r-leaf-shape-p tree)
    (equal height 0))
   ((and
     (v0r-node-shape-p tree)
     (equal (v0r-node-color tree) :v0r-red))
    (let ((left (v0r-node-left tree))
          (right (v0r-node-right tree)))
      (and
       (v0r-rbtree-p height left)
       (v0r-rbtree-p height right)
       (v0r-is-not-red-p left)
       (v0r-is-not-red-p right))))
   ((and
     (v0r-node-shape-p tree)
     (equal (v0r-node-color tree) :v0r-black))
    (and
     (v0r-rbtree-p
      (- height 1)
      (v0r-node-left tree))
     (v0r-rbtree-p
      (- height 1)
      (v0r-node-right tree))))
   (t nil)))

;; The black height remains an internal existential, as in the source
;; invariant; it is not exposed as an additional statement parameter.

(defun-sk v0r-has-black-height-p (tree)
  (exists (height)
    (and
     (integerp height)
     (v0r-rbtree-p height tree))))

(defun v0r-inv-p (default tree)
  (and
   (integerp default)
   (v0r-tree-p tree)
   (v0r-bst-p tree)
   (v0r-has-black-height-p tree)))

;; Absence quantifies over every integer value. Map membership returns a
;; stored value when present and otherwise exactly the default.

(defun-sk v0r-key-absent-p (tree key)
  (forall (value)
    (implies
     (integerp value)
     (not (v0r-memt-p tree key value)))))

(defun v0r-map-mem-p (default tree key value)
  (and
   (integerp default)
   (v0r-tree-p tree)
   (integerp key)
   (integerp value)
   (or
    (v0r-memt-p tree key value)
    (and
     (equal value default)
     (v0r-key-absent-p tree key)))))

;; This is the exact universally quantified membership relation in the
;; remove postcondition.

(defun-sk v0r-remove-membership-post-p
    (default old-tree key new-tree)
  (forall (other-key other-value)
    (implies
     (and
      (integerp other-key)
      (integerp other-value))
     (iff
      (v0r-map-mem-p
       default new-tree other-key other-value)
      (if (equal other-key key)
          (equal other-value default)
        (v0r-map-mem-p
         default old-tree other-key other-value))))))

(defun v0r-remove-post-state-p
    (default old-tree key new-tree)
  (and
   (v0r-inv-p default new-tree)
   (v0r-remove-membership-post-p
    default old-tree key new-tree)))

;; The exported VC universally quantifies the possible post-state and retains
;; its source implication unchanged: the complete post-state condition in the
;; antecedent implies that same complete condition in the consequent.

(defun-sk v0r-remove-all-post-states-p
    (default old-tree key)
  (forall (new-tree)
    (implies
     (v0r-tree-p new-tree)
     (implies
      (v0r-remove-post-state-p
       default old-tree key new-tree)
      (v0r-remove-post-state-p
       default old-tree key new-tree)))))

(defun
    ntp4vc-pearl-vacid-0-red-black-trees-vacid0-removeqtvc-statement
    (default old-tree key)
  (implies
   (and
    (integerp key)
    (v0r-inv-p default old-tree))
   (and
    (v0r-inv-p default old-tree)
    (v0r-remove-all-post-states-p
     default old-tree key))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
