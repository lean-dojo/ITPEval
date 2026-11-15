;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/pairing_heap_PairingHeap_delete_minqtvc: the delete-min verification
;; condition for a nonempty pairing heap, preserving the child-forest
;; invariant, size, and element occurrences. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; The source element type is represented by ACL2's full object universe.
;; This conservative interface supplies its arbitrary order relation; the
;; reflexivity, transitivity, and totality laws remain explicit premises.

(defstub pdm-le-op (left right) t)

(defun pdm-le-p (left right)
  (if (pdm-le-op left right) t nil))

(defun-sk pdm-reflexive-p ()
  (forall (element)
    (pdm-le-p element element)))

(defun-sk pdm-transitive-p ()
  (forall (left middle right)
    (implies
     (and
      (pdm-le-p left middle)
      (pdm-le-p middle right))
     (pdm-le-p left right))))

(defun-sk pdm-total-p ()
  (forall (left right)
    (or
     (pdm-le-p left right)
     (pdm-le-p right left))))

(defun pdm-order-laws-p ()
  (and
   (pdm-reflexive-p)
   (pdm-transitive-p)
   (pdm-total-p)))

;; The empty raw heap is NIL. A nonempty raw heap is the exact record
;; (:PAIRING-HEAP tree), and a tree is the exact record
;; (:PAIRING-TREE element children), where CHILDREN is a proper list of
;; trees. These recognizers preserve the source's mutually nested finite
;; inductive domains.

(defun pdm-heap-node-shape-p (heap)
  (and
   (true-listp heap)
   (equal (len heap) 2)
   (equal (car heap) :pairing-heap)))

(defun pdm-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 3)
   (equal (car tree) :pairing-tree)))

(defun pdm-heap-node (tree)
  (list :pairing-heap tree))

(defun pdm-tree-node (element children)
  (list :pairing-tree element children))

(defun pdm-heap-tree (heap)
  (cadr heap))

(defun pdm-tree-element (tree)
  (cadr tree))

(defun pdm-tree-children (tree)
  (caddr tree))

(defun pdm-well-formed-p (kind object)
  (declare (xargs :measure (acl2-count object)))
  (cond
   ((equal kind :raw-heap)
    (if (equal object nil)
        t
      (and
       (pdm-heap-node-shape-p object)
       (pdm-well-formed-p
        :tree
        (pdm-heap-tree object)))))
   ((equal kind :tree)
    (and
     (pdm-tree-node-shape-p object)
     (pdm-well-formed-p
      :tree-list
      (pdm-tree-children object))))
   ((equal kind :tree-list)
    (if (consp object)
        (and
         (pdm-well-formed-p :tree (car object))
         (pdm-well-formed-p :tree-list (cdr object)))
      (equal object nil)))
   (t nil)))

(defun pdm-raw-heap-p (heap)
  (pdm-well-formed-p :raw-heap heap))

(defun pdm-tree-p (tree)
  (pdm-well-formed-p :tree tree))

(defun pdm-tree-list-p (trees)
  (pdm-well-formed-p :tree-list trees))

;; SIZE-HEAP, SIZE-TREE, and SIZE-LIST are the three source functions,
;; represented by one well-founded recursion over the corresponding kind.

(defun pdm-size-of (kind object)
  (declare (xargs :measure (acl2-count object)))
  (cond
   ((equal kind :raw-heap)
    (if (equal object nil)
        0
      (if (pdm-heap-node-shape-p object)
          (pdm-size-of :tree (pdm-heap-tree object))
        0)))
   ((equal kind :tree)
    (if (pdm-tree-node-shape-p object)
        (+
         1
         (pdm-size-of
          :tree-list
          (pdm-tree-children object)))
      0))
   ((equal kind :tree-list)
    (if (consp object)
        (+
         (pdm-size-of :tree (car object))
         (pdm-size-of :tree-list (cdr object)))
      0))
   (t 0)))

(defun pdm-size-heap (heap)
  (pdm-size-of :raw-heap heap))

(defun pdm-size-list (trees)
  (pdm-size-of :tree-list trees))

;; OCC-HEAP, OCC-TREE, and OCC-LIST likewise retain the exact recursive
;; multiplicity semantics over the whole arbitrary element domain.

(defun pdm-occ-of (kind element object)
  (declare (xargs :measure (acl2-count object)))
  (cond
   ((equal kind :raw-heap)
    (if (equal object nil)
        0
      (if (pdm-heap-node-shape-p object)
          (pdm-occ-of
           :tree element (pdm-heap-tree object))
        0)))
   ((equal kind :tree)
    (if (pdm-tree-node-shape-p object)
        (+
         (if (equal element
                    (pdm-tree-element object))
             1
           0)
         (pdm-occ-of
          :tree-list
          element
          (pdm-tree-children object)))
      0))
   ((equal kind :tree-list)
    (if (consp object)
        (+
         (pdm-occ-of :tree element (car object))
         (pdm-occ-of :tree-list element (cdr object)))
      0))
   (t 0)))

(defun pdm-occ-heap (element heap)
  (pdm-occ-of :raw-heap element heap))

(defun pdm-occ-list (element trees)
  (pdm-occ-of :tree-list element trees))

(defun pdm-le-tree-p (element tree)
  (and
   (pdm-tree-node-shape-p tree)
   (pdm-le-p element
             (pdm-tree-element tree))))

(defun pdm-le-roots-p (element trees)
  (declare (xargs :measure (acl2-count trees)))
  (if (consp trees)
      (and
       (pdm-le-tree-p element (car trees))
       (pdm-le-roots-p element (cdr trees)))
    (equal trees nil)))

;; This single kind-indexed recursion is definitionally the source's mutual
;; HEAP, HEAP-TREE, and HEAP-LIST predicates.

(defun pdm-heap-structure-p (kind object)
  (declare (xargs :measure (acl2-count object)))
  (cond
   ((equal kind :raw-heap)
    (if (equal object nil)
        t
      (and
       (pdm-heap-node-shape-p object)
       (pdm-heap-structure-p
        :tree
        (pdm-heap-tree object)))))
   ((equal kind :tree)
    (and
     (pdm-tree-node-shape-p object)
     (pdm-le-roots-p
      (pdm-tree-element object)
      (pdm-tree-children object))
     (pdm-heap-structure-p
      :tree-list
      (pdm-tree-children object))))
   ((equal kind :tree-list)
    (if (consp object)
        (and
         (pdm-heap-structure-p :tree (car object))
         (pdm-heap-structure-p
          :tree-list
          (cdr object)))
      (equal object nil)))
   (t nil)))

(defun pdm-heap-p (heap)
  (pdm-heap-structure-p :raw-heap heap))

(defun pdm-heap-list-p (trees)
  (pdm-heap-structure-p :tree-list trees))

;; MINIMUM-TREE and MINIMUM are arbitrary except for their two exact source
;; equations on tree roots and nonempty raw heaps.

(defstub pdm-minimum-tree (tree) t)
(defstub pdm-minimum (heap) t)

(defun-sk pdm-minimum-tree-law-p ()
  (forall (element children)
    (implies
     (pdm-tree-list-p children)
     (equal
      (pdm-minimum-tree
       (pdm-tree-node element children))
      element))))

(defun-sk pdm-minimum-law-p ()
  (forall (tree)
    (implies
     (pdm-tree-p tree)
     (equal
      (pdm-minimum (pdm-heap-node tree))
      (pdm-minimum-tree tree)))))

;; This is the first match expression in the verification condition.

(defun pdm-child-forest-invariant-p (heap)
  (if (equal heap nil)
      nil
    (and
     (pdm-heap-node-shape-p heap)
     (pdm-heap-list-p
      (pdm-tree-children
       (pdm-heap-tree heap))))))

(defun-sk pdm-result-occurrences-p
    (result children)
  (forall (element)
    (equal
     (pdm-occ-heap element result)
     (pdm-occ-list element children))))

(defun pdm-result-premise-p (heap result)
  (if (equal heap nil)
      nil
    (let ((children
           (pdm-tree-children
            (pdm-heap-tree heap))))
      (and
       (equal
        (pdm-size-heap result)
        (pdm-size-list children))
       (pdm-result-occurrences-p
        result children)))))

(defun-sk pdm-other-occurrences-p
    (result heap minimum)
  (forall (element)
    (implies
     (not (equal element minimum))
     (equal
      (pdm-occ-heap element result)
      (pdm-occ-heap element heap)))))

(defun pdm-result-postcondition-p (heap result)
  (let ((minimum (pdm-minimum heap)))
    (and
     (equal
      (pdm-occ-heap minimum result)
      (- (pdm-occ-heap minimum heap) 1))
     (pdm-other-occurrences-p
      result heap minimum)
     (equal
      (pdm-size-heap result)
      (- (pdm-size-heap heap) 1)))))

;; RESULT remains universally quantified over the complete source heap
;; subtype, represented by raw heaps satisfying the pairing-heap invariant.

(defun-sk pdm-all-results-p (heap)
  (forall (result)
    (implies
     (and
      (pdm-raw-heap-p result)
      (pdm-heap-p result)
      (pdm-result-premise-p heap result))
     (pdm-result-postcondition-p
      heap result))))

(defun-sk
  ntp4vc-pearl-pairing-heap-pairingheap-delete-minqtvc-statement
  ()
  (forall (heap)
    (implies
     (and
      (pdm-order-laws-p)
      (pdm-minimum-tree-law-p)
      (pdm-minimum-law-p)
      (pdm-raw-heap-p heap)
      (pdm-heap-p heap)
      (< 0 (pdm-size-heap heap)))
     (and
      (pdm-child-forest-invariant-p heap)
      (pdm-all-results-p heap)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
