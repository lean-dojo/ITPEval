;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/braun_trees_BraunHeaps_addqtvc: the Braun-heap insertion
;; verification condition, preserving heap order, Braun balance, tree size,
;; and element occurrences. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst
 (remove1 'error *valid-output-names*))

;; The source element type is represented by ACL2's full object universe.
;; This conservative interface supplies its arbitrary order relation; the
;; reflexivity, transitivity, and totality laws remain explicit premises.

(defstub bta-le-op (left right) t)

(defun bta-le-p (left right)
  (if (bta-le-op left right) t nil))

(defun-sk bta-reflexive-p ()
  (forall (element)
    (bta-le-p element element)))

(defun-sk bta-transitive-p ()
  (forall (left middle right)
    (implies
     (and
      (bta-le-p left middle)
      (bta-le-p middle right))
     (bta-le-p left right))))

(defun-sk bta-total-p ()
  (forall (left right)
    (or
     (bta-le-p left right)
     (bta-le-p right left))))

(defun bta-order-laws-p ()
  (and
   (bta-reflexive-p)
   (bta-transitive-p)
   (bta-total-p)))

;; Empty trees are NIL. Nodes are exact records
;; (:BRAUN-NODE left element right), preserving the finite inductive tree
;; domain from the source.

(defun bta-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :braun-node)))

(defun bta-tree-left (tree)
  (cadr tree))

(defun bta-tree-element (tree)
  (caddr tree))

(defun bta-tree-right (tree)
  (cadddr tree))

(defun bta-node (left element right)
  (list :braun-node left element right))

(defun bta-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (bta-node-shape-p tree)
     (bta-tree-p (bta-tree-left tree))
     (bta-tree-p (bta-tree-right tree)))))

(defun bta-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (bta-node-shape-p tree)
        (+
         1
         (bta-size (bta-tree-left tree))
         (bta-size (bta-tree-right tree)))
      0)))

(defun bta-occ (element tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (bta-node-shape-p tree)
        (+
         (if (equal element
                    (bta-tree-element tree))
             1
           0)
         (bta-occ element
                  (bta-tree-left tree))
         (bta-occ element
                  (bta-tree-right tree)))
      0)))

(defun bta-le-root-p (element tree)
  (if (equal tree nil)
      t
    (bta-le-p element
              (bta-tree-element tree))))

(defun bta-heap-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (bta-node-shape-p tree)
        (let ((left (bta-tree-left tree))
              (element (bta-tree-element tree))
              (right (bta-tree-right tree)))
          (and
           (bta-le-root-p element left)
           (bta-heap-p left)
           (bta-le-root-p element right)
           (bta-heap-p right)))
      nil)))

(defun bta-inv-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (bta-node-shape-p tree)
        (let ((left (bta-tree-left tree))
              (right (bta-tree-right tree)))
          (and
           (or
            (equal (bta-size left)
                   (bta-size right))
            (equal (bta-size left)
                   (+ (bta-size right) 1)))
           (bta-inv-p left)
           (bta-inv-p right)))
      nil)))

;; The first source conjunct exposes the right subtree in the nonempty case
;; and records the same structural disjunction produced by matching the
;; original tree a second time.

(defun bta-right-subtree-condition-p (tree)
  (if (equal tree nil)
      t
    (let ((left (bta-tree-left tree))
          (right (bta-tree-right tree)))
      (and
       (or
        (equal left right)
        (equal right right))
       (bta-heap-p right)
       (bta-inv-p right)))))

;; These predicates retain the source universal quantifiers over every
;; element distinct from the newly counted root element.

(defun-sk bta-other-occurrences-p
    (new-tree old-tree excluded)
  (forall (element)
    (implies
     (not (equal element excluded))
     (equal
      (bta-occ element new-tree)
      (bta-occ element old-tree)))))

(defun-sk bta-less-or-equal-branch-p
    (left old-root right inserted result)
  (exists (added-right)
    (and
     (bta-tree-p added-right)
     (bta-heap-p added-right)
     (bta-inv-p added-right)
     (equal
      (bta-occ old-root added-right)
      (+ (bta-occ old-root right) 1))
     (bta-other-occurrences-p
      added-right right old-root)
     (equal
      (bta-size added-right)
      (+ (bta-size right) 1))
     (equal
      result
      (bta-node added-right inserted left)))))

(defun-sk bta-greater-branch-p
    (left old-root right inserted result)
  (exists (added-right)
    (and
     (bta-tree-p added-right)
     (bta-heap-p added-right)
     (bta-inv-p added-right)
     (equal
      (bta-occ inserted added-right)
      (+ (bta-occ inserted right) 1))
     (bta-other-occurrences-p
      added-right right inserted)
     (equal
      (bta-size added-right)
      (+ (bta-size right) 1))
     (equal
      result
      (bta-node added-right old-root left)))))

(defun bta-result-premise-p (tree inserted result)
  (if (equal tree nil)
      (equal
       result
       (bta-node nil inserted nil))
    (let ((left (bta-tree-left tree))
          (old-root (bta-tree-element tree))
          (right (bta-tree-right tree)))
      (if (bta-le-p inserted old-root)
          (bta-less-or-equal-branch-p
           left old-root right inserted result)
        (bta-greater-branch-p
         left old-root right inserted result)))))

(defun bta-result-postcondition-p (tree inserted result)
  (and
   (bta-heap-p result)
   (bta-inv-p result)
   (equal
    (bta-occ inserted result)
    (+ (bta-occ inserted tree) 1))
   (bta-other-occurrences-p
    result tree inserted)
   (equal
    (bta-size result)
    (+ (bta-size tree) 1))))

(defun-sk bta-all-results-p (tree inserted)
  (forall (result)
    (implies
     (and
      (bta-tree-p result)
      (bta-result-premise-p
       tree inserted result))
     (bta-result-postcondition-p
      tree inserted result))))

(defun-sk
  ntp4vc-pearl-braun-trees-braunheaps-addqtvc-statement
  ()
  (forall (tree inserted)
    (implies
     (and
      (bta-order-laws-p)
      (bta-tree-p tree)
      (bta-heap-p tree)
      (bta-inv-p tree))
     (and
      (bta-right-subtree-condition-p tree)
      (bta-all-results-p tree inserted)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
