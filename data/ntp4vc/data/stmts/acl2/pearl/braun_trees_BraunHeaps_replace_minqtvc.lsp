;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/braun_trees_BraunHeaps_replace_minqtvc: the Braun-heap minimum
;; replacement verification condition, preserving heap order, Braun balance,
;; tree size, and element occurrences. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst
 (remove1 'error *valid-output-names*))
(set-gag-mode t)

;; The source element type is represented by ACL2's full object universe.
;; These conservative interfaces supply its arbitrary order relation and
;; minimum operation. Their source laws remain explicit statement premises.

(defstub brm-le-op (left right) t)

(defun brm-le-p (left right)
  (if (brm-le-op left right) t nil))

(defun-sk brm-reflexive-p ()
  (forall (element)
    (brm-le-p element element)))

(defun-sk brm-transitive-p ()
  (forall (left middle right)
    (implies
     (and
      (brm-le-p left middle)
      (brm-le-p middle right))
     (brm-le-p left right))))

(defun-sk brm-total-p ()
  (forall (left right)
    (or
     (brm-le-p left right)
     (brm-le-p right left))))

(defun brm-order-laws-p ()
  (and
   (brm-reflexive-p)
   (brm-transitive-p)
   (brm-total-p)))

;; Empty trees are NIL. Nodes are exact records
;; (:BRAUN-NODE left element right), preserving the source's finite
;; inductive binary-tree domain while element labels remain arbitrary.

(defun brm-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :braun-node)))

(defun brm-tree-left (tree)
  (cadr tree))

(defun brm-tree-element (tree)
  (caddr tree))

(defun brm-tree-right (tree)
  (cadddr tree))

(defun brm-node (left element right)
  (list :braun-node left element right))

(defun brm-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (brm-node-shape-p tree)
     (brm-tree-p (brm-tree-left tree))
     (brm-tree-p (brm-tree-right tree)))))

(defun brm-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (brm-node-shape-p tree)
        (+
         1
         (brm-size (brm-tree-left tree))
         (brm-size (brm-tree-right tree)))
      0)))

(defun brm-occ (element tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (brm-node-shape-p tree)
        (+
         (if (equal element
                    (brm-tree-element tree))
             1
           0)
         (brm-occ element
                  (brm-tree-left tree))
         (brm-occ element
                  (brm-tree-right tree)))
      0)))

(defun brm-le-root-p (element tree)
  (if (equal tree nil)
      t
    (brm-le-p element
              (brm-tree-element tree))))

(defun brm-heap-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (brm-node-shape-p tree)
        (let ((left (brm-tree-left tree))
              (element (brm-tree-element tree))
              (right (brm-tree-right tree)))
          (and
           (brm-le-root-p element left)
           (brm-heap-p left)
           (brm-le-root-p element right)
           (brm-heap-p right)))
      nil)))

(defun brm-inv-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (brm-node-shape-p tree)
        (let ((left (brm-tree-left tree))
              (right (brm-tree-right tree)))
          (and
           (or
            (equal (brm-size left)
                   (brm-size right))
            (equal (brm-size left)
                   (+ (brm-size right) 1)))
           (brm-inv-p left)
           (brm-inv-p right)))
      nil)))

(defstub brm-minimum (tree) t)

(defun-sk brm-minimum-law-p ()
  (forall (left element right)
    (implies
     (and
      (brm-tree-p left)
      (brm-tree-p right))
     (equal
      (brm-minimum
       (brm-node left element right))
      element))))

;; ACL2 Booleans T and NIL represent the source's two-element Bool type.

(defun brm-boolean-p (value)
  (or
   (equal value t)
   (equal value nil)))

(defun brm-o1-equation-p
    (inserted left right o1)
  (equal
   o1
   (if (brm-le-root-p inserted left)
       (if (brm-le-root-p inserted right)
           t
         nil)
     nil)))

;; Preserve the universal occurrence equation for every element distinct
;; from the inserted element and the old minimum.

(defun-sk brm-other-occurrences-p
    (new-tree old-tree excluded1 excluded2)
  (forall (element)
    (implies
     (and
      (not (equal element excluded1))
      (not (equal element excluded2)))
     (equal
      (brm-occ element new-tree)
      (brm-occ element old-tree)))))

;; This is the source replacement relation for an internally quantified
;; result tree. It preserves heap order, Braun balance, size, and the exact
;; conditional update of the two distinguished occurrence counts.

(defun brm-replacement-p
    (new-tree old-tree inserted)
  (let ((old-minimum (brm-minimum old-tree)))
    (and
     (brm-tree-p new-tree)
     (brm-heap-p new-tree)
     (brm-inv-p new-tree)
     (if (equal inserted old-minimum)
         (equal
          (brm-occ inserted new-tree)
          (brm-occ inserted old-tree))
       (and
        (equal
         (brm-occ inserted new-tree)
         (+ (brm-occ inserted old-tree) 1))
        (equal
         (brm-occ old-minimum new-tree)
         (- (brm-occ old-minimum old-tree) 1))))
     (brm-other-occurrences-p
      new-tree old-tree inserted old-minimum)
     (equal
      (brm-size new-tree)
      (brm-size old-tree)))))

;; This retains the source universal quantifier over every possible
;; replacement of the right subtree in the first conclusion's final branch.

(defun-sk brm-right-recursive-condition-p
    (right inserted)
  (forall (replacement)
    (implies
     (brm-replacement-p replacement right inserted)
     (and
      (brm-heap-p right)
      (< 0 (brm-size right))))))

;; The repeated source match on TREE is kept as the corresponding child
;; disjunction, even though LEFT and RIGHT were obtained from that same node.

(defun brm-left-branch-condition-p
    (tree left)
  (and
   (or
    (equal (brm-tree-left tree) left)
    (equal (brm-tree-right tree) left))
   (brm-heap-p left)
   (brm-inv-p left)
   (< 0 (brm-size left))))

(defun brm-right-branch-condition-p
    (tree right inserted)
  (and
   (or
    (equal (brm-tree-left tree) right)
    (equal (brm-tree-right tree) right))
   (brm-heap-p right)
   (brm-inv-p right)
   (< 0 (brm-size right))
   (brm-right-recursive-condition-p
    right inserted)))

(defun brm-first-o1-consequence-p
    (tree inserted)
  (let ((left (brm-tree-left tree))
        (right (brm-tree-right tree)))
    (and
     (brm-heap-p left)
     (< 0 (brm-size left))
     (if (brm-le-root-p
          (brm-minimum left)
          right)
         (brm-left-branch-condition-p
          tree left)
       (brm-right-branch-condition-p
        tree right inserted)))))

(defun-sk brm-first-node-conclusion-p
    (tree inserted)
  (forall (o1)
    (implies
     (and
      (brm-boolean-p o1)
      (brm-o1-equation-p
       inserted
       (brm-tree-left tree)
       (brm-tree-right tree)
       o1)
      (not (equal o1 t)))
     (brm-first-o1-consequence-p
      tree inserted))))

(defun brm-first-conclusion-p
    (tree inserted)
  (if (equal tree nil)
      nil
    (brm-first-node-conclusion-p
     tree inserted)))

;; The recursive O2 witnesses remain existentially quantified inside the
;; two branches of the source result relation.

(defun-sk brm-left-rebuild-p
    (left right inserted result)
  (exists (replacement)
    (and
     (brm-replacement-p
      replacement left inserted)
     (equal
      result
      (brm-node replacement
                (brm-minimum left)
                right)))))

(defun-sk brm-right-rebuild-p
    (left right inserted result)
  (exists (replacement)
    (and
     (brm-replacement-p
      replacement right inserted)
     (equal
      result
      (brm-node left
                (brm-minimum right)
                replacement)))))

(defun-sk brm-node-result-premise-p
    (tree inserted result)
  (exists (o1)
    (and
     (brm-boolean-p o1)
     (brm-o1-equation-p
      inserted
      (brm-tree-left tree)
      (brm-tree-right tree)
      o1)
     (if (equal o1 t)
         (equal
          result
          (brm-node
           (brm-tree-left tree)
           inserted
           (brm-tree-right tree)))
       (if (brm-le-root-p
            (brm-minimum
             (brm-tree-left tree))
            (brm-tree-right tree))
           (brm-left-rebuild-p
            (brm-tree-left tree)
            (brm-tree-right tree)
            inserted
            result)
         (brm-right-rebuild-p
          (brm-tree-left tree)
          (brm-tree-right tree)
          inserted
          result))))))

(defun brm-result-premise-p
    (tree inserted result)
  (if (equal tree nil)
      nil
    (brm-node-result-premise-p
     tree inserted result)))

;; RESULT retains its source universal quantifier over the inductive tree
;; domain, and the source postcondition is exactly BRM-REPLACEMENT-P.

(defun-sk brm-all-results-p
    (tree inserted)
  (forall (result)
    (implies
     (and
      (brm-tree-p result)
      (brm-result-premise-p
       tree inserted result))
     (brm-replacement-p
      result tree inserted))))

(defun-sk
  ntp4vc-pearl-braun-trees-braunheaps-replace-minqtvc-statement
  ()
  (forall (tree inserted)
    (implies
     (and
      (brm-order-laws-p)
      (brm-minimum-law-p)
      (brm-tree-p tree)
      (brm-heap-p tree)
      (brm-inv-p tree)
      (< 0 (brm-size tree)))
     (and
      (brm-first-conclusion-p
       tree inserted)
      (brm-all-results-p
       tree inserted)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
