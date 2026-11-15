;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/braun_trees_BraunHeaps_mergeqtvc: the Braun-heap merge verification
;; condition, preserving heap order, Braun balance, tree size, and element
;; occurrences across the two input trees. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; The source element type is represented by ACL2's full object universe.
;; This conservative interface supplies its arbitrary order relation; the
;; reflexivity, transitivity, and totality laws remain explicit premises.

(defstub btm-le-op (left right) t)

(defun btm-le-p (left right)
  (if (btm-le-op left right) t nil))

(defun-sk btm-reflexive-p ()
  (forall (element)
    (btm-le-p element element)))

(defun-sk btm-transitive-p ()
  (forall (left middle right)
    (implies
     (and
      (btm-le-p left middle)
      (btm-le-p middle right))
     (btm-le-p left right))))

(defun-sk btm-total-p ()
  (forall (left right)
    (or
     (btm-le-p left right)
     (btm-le-p right left))))

(defun btm-order-laws-p ()
  (and
   (btm-reflexive-p)
   (btm-transitive-p)
   (btm-total-p)))

;; Empty trees are NIL. Nodes are exact records
;; (:BRAUN-NODE left element right), preserving the source's finite
;; inductive binary-tree domain while element labels remain arbitrary.

(defun btm-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :braun-node)))

(defun btm-tree-left (tree)
  (cadr tree))

(defun btm-tree-element (tree)
  (caddr tree))

(defun btm-tree-right (tree)
  (cadddr tree))

(defun btm-node (left element right)
  (list :braun-node left element right))

(defun btm-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (btm-node-shape-p tree)
     (btm-tree-p (btm-tree-left tree))
     (btm-tree-p (btm-tree-right tree)))))

(defun btm-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (btm-node-shape-p tree)
        (+
         1
         (btm-size (btm-tree-left tree))
         (btm-size (btm-tree-right tree)))
      0)))

(defun btm-occ (element tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (btm-node-shape-p tree)
        (+
         (if (equal element
                    (btm-tree-element tree))
             1
           0)
         (btm-occ element
                  (btm-tree-left tree))
         (btm-occ element
                  (btm-tree-right tree)))
      0)))

(defun btm-le-root-p (element tree)
  (if (equal tree nil)
      t
    (btm-le-p element
              (btm-tree-element tree))))

(defun btm-heap-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (btm-node-shape-p tree)
        (let ((left (btm-tree-left tree))
              (element (btm-tree-element tree))
              (right (btm-tree-right tree)))
          (and
           (btm-le-root-p element left)
           (btm-heap-p left)
           (btm-le-root-p element right)
           (btm-heap-p right)))
      nil)))

(defun btm-inv-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (btm-node-shape-p tree)
        (let ((left (btm-tree-left tree))
              (right (btm-tree-right tree)))
          (and
           (or
            (equal (btm-size left)
                   (btm-size right))
            (equal (btm-size left)
                   (+ (btm-size right) 1)))
           (btm-inv-p left)
           (btm-inv-p right)))
      nil)))

;; The source minimum function is constrained to return a node's root.
;; It is used only in a branch where the right tree has already matched a
;; node, so this definition is extensionally identical on every relevant
;; argument; its arbitrary empty-tree value is immaterial.

(defun btm-minimum (tree)
  (if (equal tree nil)
      nil
    (btm-tree-element tree)))

;; Universal occurrence equations retain their quantification over the full
;; arbitrary element domain.

(defun-sk btm-other-occurrences-p
    (new-tree old-tree excluded)
  (forall (element)
    (implies
     (not (equal element excluded))
     (equal
      (btm-occ element new-tree)
      (btm-occ element old-tree)))))

(defun-sk btm-occ-sum-p (target left right)
  (forall (element)
    (equal
     (btm-occ element target)
     (+
      (btm-occ element left)
      (btm-occ element right)))))

(defun-sk btm-other-than-two-occurrences-p
    (new-tree old-tree excluded1 excluded2)
  (forall (element)
    (implies
     (and
      (not (equal element excluded1))
      (not (equal element excluded2)))
     (equal
      (btm-occ element new-tree)
      (btm-occ element old-tree)))))

;; This is the universal implication in the first conclusion's branch where
;; the left root is not below the right root. The reduced left tree remains a
;; universally quantified source-typed tree, not an external parameter.

(defun-sk btm-recursive-right-condition-p
    (left right)
  (forall (extracted reduced-left)
    (implies
     (and
      (btm-tree-p reduced-left)
      (btm-heap-p reduced-left)
      (btm-inv-p reduced-left)
      (equal
       (btm-size reduced-left)
       (- (btm-size left) 1))
      (equal
       (btm-occ extracted reduced-left)
       (- (btm-occ extracted left) 1))
      (btm-other-occurrences-p
       reduced-left left extracted))
     (and
      (btm-heap-p right)
      (btm-inv-p right)
      (< 0 (btm-size right))))))

;; Exact case split for the theorem's first match expression.

(defun btm-first-conclusion-p (left right)
  (cond
   ((equal right nil)
    t)
   ((equal left nil)
    nil)
   (t
    (let ((left-left (btm-tree-left left))
          (left-root (btm-tree-element left))
          (left-right (btm-tree-right left))
          (right-root (btm-tree-element right)))
      (if (btm-le-p left-root right-root)
          (and
           (<= 0
               (+ (btm-size left)
                  (btm-size right)))
           (< (+ (btm-size left-left)
                 (btm-size left-right))
              (+ (btm-size left)
                 (btm-size right)))
           (btm-heap-p left-left)
           (btm-heap-p left-right)
           (btm-inv-p left-left)
           (btm-inv-p left-right)
           (<= (btm-size left-right)
               (btm-size left-left))
           (<= (btm-size left-left)
               (+ (btm-size left-right) 1)))
        (and
         (btm-heap-p left)
         (btm-inv-p left)
         (< 0 (btm-size left))
         (btm-recursive-right-condition-p
          left right)))))))

;; In the below-root branch, MERGED-CHILDREN is the source's internal O1
;; witness and RESULT is reconstructed exactly as Node right left-root O1.

(defun-sk btm-below-root-result-p
    (left-left left-root left-right right result)
  (exists (merged-children)
    (and
     (btm-tree-p merged-children)
     (btm-heap-p merged-children)
     (btm-inv-p merged-children)
     (btm-occ-sum-p
      merged-children left-left left-right)
     (equal
      (btm-size merged-children)
      (+ (btm-size left-left)
         (btm-size left-right)))
     (equal
      result
      (btm-node right left-root merged-children)))))

;; This preserves the occurrence update for the right-side replacement tree,
;; including the source conditional when the extracted element is the right
;; root and the universal equation for every other element.

(defun btm-right-replacement-p
    (right extracted replacement)
  (let ((minimum (btm-minimum right)))
    (and
     (btm-tree-p replacement)
     (btm-heap-p replacement)
     (btm-inv-p replacement)
     (if (equal extracted minimum)
         (equal
          (btm-occ extracted replacement)
          (btm-occ extracted right))
       (and
        (equal
         (btm-occ extracted replacement)
         (+ (btm-occ extracted right) 1))
        (equal
         (btm-occ minimum replacement)
         (- (btm-occ minimum right) 1))))
     (btm-other-than-two-occurrences-p
      replacement right extracted minimum)
     (equal
      (btm-size replacement)
      (btm-size right)))))

;; REPLACEMENT is the nested source existential O1. The result constructor
;; uses the original right root and the recursively reduced left tree.

(defun-sk btm-right-rebuild-result-p
    (right right-root extracted reduced-left result)
  (exists (replacement)
    (and
     (btm-right-replacement-p
      right extracted replacement)
     (equal
      result
      (btm-node replacement
                right-root
                reduced-left)))))

;; EXTRACTED and REDUCED-LEFT preserve the outer existential witnesses of the
;; source branch where the left root is not below the right root.

(defun-sk btm-above-root-result-p
    (left right right-root result)
  (exists (extracted reduced-left)
    (and
     (btm-tree-p reduced-left)
     (btm-heap-p reduced-left)
     (btm-inv-p reduced-left)
     (equal
      (btm-size reduced-left)
      (- (btm-size left) 1))
     (equal
      (btm-occ extracted reduced-left)
      (- (btm-occ extracted left) 1))
     (btm-other-occurrences-p
      reduced-left left extracted)
     (btm-right-rebuild-result-p
      right right-root extracted reduced-left result))))

;; Exact case split forming the antecedent of the universally quantified
;; merge postcondition.

(defun btm-result-premise-p (left right result)
  (cond
   ((equal right nil)
    (equal result left))
   ((equal left nil)
    nil)
   (t
    (let ((left-left (btm-tree-left left))
          (left-root (btm-tree-element left))
          (left-right (btm-tree-right left))
          (right-root (btm-tree-element right)))
      (if (btm-le-p left-root right-root)
          (btm-below-root-result-p
           left-left left-root left-right right result)
        (btm-above-root-result-p
         left right right-root result))))))

(defun btm-result-postcondition-p
    (left right result)
  (and
   (btm-heap-p result)
   (btm-inv-p result)
   (btm-occ-sum-p result left right)
   (equal
    (btm-size result)
    (+ (btm-size left)
       (btm-size right)))))

;; RESULT retains its source universal quantifier over the exact tree domain.

(defun-sk btm-all-results-p (left right)
  (forall (result)
    (implies
     (and
      (btm-tree-p result)
      (btm-result-premise-p
       left right result))
     (btm-result-postcondition-p
      left right result))))

(defun-sk
  ntp4vc-pearl-braun-trees-braunheaps-mergeqtvc-statement
  ()
  (forall (left right)
    (implies
     (and
      (btm-order-laws-p)
      (btm-tree-p left)
      (btm-tree-p right)
      (btm-heap-p left)
      (btm-heap-p right)
      (btm-inv-p left)
      (btm-inv-p right)
      (<= (btm-size right)
          (btm-size left))
      (<= (btm-size left)
          (+ (btm-size right) 1)))
     (and
      (btm-first-conclusion-p left right)
      (btm-all-results-p left right)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
