;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/braun_trees_BraunHeaps_extractqtvc: the Braun-heap extraction
;; verification condition, preserving heap order, Braun balance, tree size,
;; and element occurrences after removal. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; The source element type is represented by ACL2's full object universe.
;; This conservative interface supplies its arbitrary order relation; the
;; reflexivity, transitivity, and totality laws remain explicit premises.

(defstub bte-le-op (left right) t)

(defun bte-le-p (left right)
  (if (bte-le-op left right) t nil))

(defun-sk bte-reflexive-p ()
  (forall (element)
    (bte-le-p element element)))

(defun-sk bte-transitive-p ()
  (forall (left middle right)
    (implies
     (and
      (bte-le-p left middle)
      (bte-le-p middle right))
     (bte-le-p left right))))

(defun-sk bte-total-p ()
  (forall (left right)
    (or
     (bte-le-p left right)
     (bte-le-p right left))))

(defun bte-order-laws-p ()
  (and
   (bte-reflexive-p)
   (bte-transitive-p)
   (bte-total-p)))

;; Empty trees are NIL. Nodes are exact records
;; (:BRAUN-NODE left element right), preserving the finite inductive tree
;; domain from the source.

(defun bte-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :braun-node)))

(defun bte-tree-left (tree)
  (cadr tree))

(defun bte-tree-element (tree)
  (caddr tree))

(defun bte-tree-right (tree)
  (cadddr tree))

(defun bte-node (left element right)
  (list :braun-node left element right))

(defun bte-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (bte-node-shape-p tree)
     (bte-tree-p (bte-tree-left tree))
     (bte-tree-p (bte-tree-right tree)))))

(defun bte-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (bte-node-shape-p tree)
        (+
         1
         (bte-size (bte-tree-left tree))
         (bte-size (bte-tree-right tree)))
      0)))

(defun bte-occ (element tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (bte-node-shape-p tree)
        (+
         (if (equal element
                    (bte-tree-element tree))
             1
           0)
         (bte-occ element
                  (bte-tree-left tree))
         (bte-occ element
                  (bte-tree-right tree)))
      0)))

(defun bte-le-root-p (element tree)
  (if (equal tree nil)
      t
    (bte-le-p element
              (bte-tree-element tree))))

(defun bte-heap-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (bte-node-shape-p tree)
        (let ((left (bte-tree-left tree))
              (element (bte-tree-element tree))
              (right (bte-tree-right tree)))
          (and
           (bte-le-root-p element left)
           (bte-heap-p left)
           (bte-le-root-p element right)
           (bte-heap-p right)))
      nil)))

(defun bte-inv-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (bte-node-shape-p tree)
        (let ((left (bte-tree-left tree))
              (right (bte-tree-right tree)))
          (and
           (or
            (equal (bte-size left)
                   (bte-size right))
            (equal (bte-size left)
                   (+ (bte-size right) 1)))
           (bte-inv-p left)
           (bte-inv-p right)))
      nil)))

;; This is the source theorem's first match expression. A node with an empty
;; left subtree satisfies it immediately; otherwise the repeated match on the
;; original node retains its structural disjunction and the left-subtree
;; heap, balance, and nonemptiness conditions.

(defun bte-first-conclusion-p (tree)
  (cond
   ((equal tree nil)
    nil)
   ((equal (bte-tree-left tree) nil)
    t)
   (t
    (let ((left (bte-tree-left tree)))
      (and
       (or
        (equal (bte-tree-left tree) left)
        (equal (bte-tree-right tree) left))
       (bte-heap-p left)
       (bte-inv-p left)
       (< 0 (bte-size left)))))))

;; Preserve each source universal quantifier over elements unequal to the
;; extracted element.

(defun-sk bte-other-occurrences-p
    (new-tree old-tree excluded)
  (forall (element)
    (implies
     (not (equal element excluded))
     (equal
      (bte-occ element new-tree)
      (bte-occ element old-tree)))))

;; In the recursive extraction branch, REDUCED-LEFT remains an internal
;; existential tree witness exactly as in the source statement.

(defun-sk bte-recursive-extraction-premise-p
    (left root right extracted result)
  (exists (reduced-left)
    (and
     (bte-tree-p reduced-left)
     (bte-heap-p reduced-left)
     (bte-inv-p reduced-left)
     (equal
      (bte-size reduced-left)
      (- (bte-size left) 1))
     (equal
      (bte-occ extracted reduced-left)
      (- (bte-occ extracted left) 1))
     (bte-other-occurrences-p
      reduced-left left extracted)
     (equal
      result
      (bte-node right root reduced-left)))))

;; Exact case split forming the antecedent of the universally quantified
;; extraction postcondition.

(defun bte-extraction-premise-p (tree extracted result)
  (cond
   ((equal tree nil)
    nil)
   ((equal (bte-tree-left tree) nil)
    (and
     (equal extracted
            (bte-tree-element tree))
     (equal result nil)))
   (t
    (bte-recursive-extraction-premise-p
     (bte-tree-left tree)
     (bte-tree-element tree)
     (bte-tree-right tree)
     extracted
     result))))

(defun bte-extraction-postcondition-p
    (tree extracted result)
  (and
   (bte-heap-p result)
   (bte-inv-p result)
   (equal
    (bte-size result)
    (- (bte-size tree) 1))
   (equal
    (bte-occ extracted result)
    (- (bte-occ extracted tree) 1))
   (bte-other-occurrences-p
    result tree extracted)))

;; The element and result tree remain universally quantified inside the
;; statement. BTE-TREE-P restricts RESULT to the source's typed tree domain.

(defun-sk bte-all-extractions-p (tree)
  (forall (extracted result)
    (implies
     (and
      (bte-tree-p result)
      (bte-extraction-premise-p
       tree extracted result))
     (bte-extraction-postcondition-p
      tree extracted result))))

(defun-sk
  ntp4vc-pearl-braun-trees-braunheaps-extractqtvc-statement
  ()
  (forall (tree)
    (implies
     (and
      (bte-order-laws-p)
      (bte-tree-p tree)
      (bte-heap-p tree)
      (bte-inv-p tree)
      (< 0 (bte-size tree)))
     (and
      (bte-first-conclusion-p tree)
      (bte-all-extractions-p tree)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
