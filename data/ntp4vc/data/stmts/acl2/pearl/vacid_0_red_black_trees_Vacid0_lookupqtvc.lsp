;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vacid_0_red_black_trees_Vacid0_lookupqtvc: the lookup verification
;; condition for an integer-keyed red-black tree map with a default value,
;; relating tree membership, absence, and returned values. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Colors and trees are exact tagged constructor records for the Why3
;; datatypes. Keys, values, and black heights retain their mathematical
;; integer domains.

(defun v0l-color-p (color)
  (or
   (equal color :v0l-red)
   (equal color :v0l-black)))

(defun v0l-leaf ()
  :v0l-leaf)

(defun v0l-node (color left key value right)
  (cons
   :v0l-node
   (cons
    color
    (cons
     left
     (cons key (cons value right))))))

(defun v0l-leaf-shape-p (tree)
  (equal tree :v0l-leaf))

(defun v0l-node-shape-p (tree)
  (and
   (consp tree)
   (equal (car tree) :v0l-node)
   (consp (cdr tree))
   (consp (cddr tree))
   (consp (cdddr tree))
   (consp (cddddr tree))))

(defun v0l-node-color (tree)
  (cadr tree))

(defun v0l-node-left (tree)
  (caddr tree))

(defun v0l-node-key (tree)
  (cadddr tree))

(defun v0l-node-value (tree)
  (car (cddddr tree)))

(defun v0l-node-right (tree)
  (cdr (cddddr tree)))

(defun v0l-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((v0l-leaf-shape-p tree)
    t)
   ((v0l-node-shape-p tree)
    (and
     (v0l-color-p (v0l-node-color tree))
     (v0l-tree-p (v0l-node-left tree))
     (integerp (v0l-node-key tree))
     (integerp (v0l-node-value tree))
     (v0l-tree-p (v0l-node-right tree))))
   (t nil)))

;; Occurrence, ordering, and the binary-search-tree invariant are direct
;; recursive renderings of the source predicates.

(defun v0l-memt-p (tree key value)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((v0l-leaf-shape-p tree)
    nil)
   ((v0l-node-shape-p tree)
    (or
     (and
      (equal key (v0l-node-key tree))
      (equal value (v0l-node-value tree)))
     (v0l-memt-p (v0l-node-left tree) key value)
     (v0l-memt-p (v0l-node-right tree) key value)))
   (t nil)))

(defun-sk v0l-lt-tree-p (bound tree)
  (forall (key value)
    (implies
     (and
      (integerp key)
      (integerp value))
     (implies
      (v0l-memt-p tree key value)
      (< key bound)))))

(defun-sk v0l-gt-tree-p (bound tree)
  (forall (key value)
    (implies
     (and
      (integerp key)
      (integerp value))
     (implies
      (v0l-memt-p tree key value)
      (< bound key)))))

(defun v0l-bst-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((v0l-leaf-shape-p tree)
    t)
   ((v0l-node-shape-p tree)
    (let ((left (v0l-node-left tree))
          (key (v0l-node-key tree))
          (right (v0l-node-right tree)))
      (and
       (v0l-bst-p left)
       (v0l-bst-p right)
       (v0l-lt-tree-p key left)
       (v0l-gt-tree-p key right))))
   (t nil)))

;; The red-black predicate preserves the source integer black-height
;; parameter and the requirement that a red node has no red child.

(defun v0l-is-not-red-p (tree)
  (cond
   ((v0l-leaf-shape-p tree)
    t)
   ((and
     (v0l-node-shape-p tree)
     (equal (v0l-node-color tree) :v0l-red))
    nil)
   ((and
     (v0l-node-shape-p tree)
     (equal (v0l-node-color tree) :v0l-black))
    t)
   (t nil)))

(defun v0l-rbtree-p (height tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((v0l-leaf-shape-p tree)
    (equal height 0))
   ((and
     (v0l-node-shape-p tree)
     (equal (v0l-node-color tree) :v0l-red))
    (let ((left (v0l-node-left tree))
          (right (v0l-node-right tree)))
      (and
       (v0l-rbtree-p height left)
       (v0l-rbtree-p height right)
       (v0l-is-not-red-p left)
       (v0l-is-not-red-p right))))
   ((and
     (v0l-node-shape-p tree)
     (equal (v0l-node-color tree) :v0l-black))
    (and
     (v0l-rbtree-p
      (- height 1)
      (v0l-node-left tree))
     (v0l-rbtree-p
      (- height 1)
      (v0l-node-right tree))))
   (t nil)))

;; The black height remains an internal existential, as in the source
;; invariant; it is not exposed as an additional statement parameter.

(defun-sk v0l-has-black-height-p (tree)
  (exists (height)
    (and
     (integerp height)
     (v0l-rbtree-p height tree))))

(defun v0l-inv-p (default tree)
  (and
   (integerp default)
   (v0l-tree-p tree)
   (v0l-bst-p tree)
   (v0l-has-black-height-p tree)))

;; Absence quantifies over every integer value. The map membership predicate
;; returns the stored value when present and otherwise exactly the default.

(defun-sk v0l-key-absent-p (tree key)
  (forall (value)
    (implies
     (integerp value)
     (not (v0l-memt-p tree key value)))))

(defun v0l-map-mem-p (default tree key value)
  (and
   (integerp default)
   (v0l-tree-p tree)
   (integerp key)
   (integerp value)
   (or
    (v0l-memt-p tree key value)
    (and
     (equal value default)
     (v0l-key-absent-p tree key)))))

;; RESULT retains the source universal quantifier. Its antecedent is the
;; exact disjunction produced by normal return from FIND or its Not_found
;; branch.

(defun-sk v0l-all-lookup-results-p (default tree key)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (or
       (v0l-memt-p tree key result)
       (and
        (v0l-key-absent-p tree key)
        (equal result default)))
      (v0l-map-mem-p
       default tree key result)))))

(defun
    ntp4vc-pearl-vacid-0-red-black-trees-vacid0-lookupqtvc-statement
    (default tree key)
  (implies
   (and
    (integerp key)
    (v0l-inv-p default tree))
   (and
    (v0l-bst-p tree)
    (v0l-all-lookup-results-p
     default tree key))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
