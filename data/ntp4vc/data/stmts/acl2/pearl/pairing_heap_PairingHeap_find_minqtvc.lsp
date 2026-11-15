;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/pairing_heap_PairingHeap_find_minqtvc: the find-minimum verification
;; condition for a nonempty pairing heap, exposing its root and identifying
;; that root with the heap minimum. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; The source element type is represented by ACL2's full object universe.
;; This conservative interface supplies its arbitrary order relation; the
;; reflexivity, transitivity, and totality laws remain explicit premises.

(defstub pfm-le-op (left right) t)

(defun pfm-le-p (left right)
  (if (pfm-le-op left right) t nil))

(defun-sk pfm-reflexive-p ()
  (forall (element)
    (pfm-le-p element element)))

(defun-sk pfm-transitive-p ()
  (forall (left middle right)
    (implies
     (and
      (pfm-le-p left middle)
      (pfm-le-p middle right))
     (pfm-le-p left right))))

(defun-sk pfm-total-p ()
  (forall (left right)
    (or
     (pfm-le-p left right)
     (pfm-le-p right left))))

(defun pfm-order-laws-p ()
  (and
   (pfm-reflexive-p)
   (pfm-transitive-p)
   (pfm-total-p)))

;; The empty raw heap is NIL. A nonempty raw heap is the exact record
;; (:PAIRING-HEAP tree), and a tree is the exact record
;; (:PAIRING-TREE element children), where CHILDREN is a proper list of
;; trees. These recognizers preserve the source's mutually nested finite
;; inductive domains.

(defun pfm-heap-node-shape-p (heap)
  (and
   (true-listp heap)
   (equal (len heap) 2)
   (equal (car heap) :pairing-heap)))

(defun pfm-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 3)
   (equal (car tree) :pairing-tree)))

(defun pfm-heap-node (tree)
  (list :pairing-heap tree))

(defun pfm-tree-node (element children)
  (list :pairing-tree element children))

(defun pfm-heap-tree (heap)
  (cadr heap))

(defun pfm-tree-element (tree)
  (cadr tree))

(defun pfm-tree-children (tree)
  (caddr tree))

(defun pfm-well-formed-p (kind object)
  (declare (xargs :measure (acl2-count object)))
  (cond
   ((equal kind :raw-heap)
    (if (equal object nil)
        t
      (and
       (pfm-heap-node-shape-p object)
       (pfm-well-formed-p
        :tree
        (pfm-heap-tree object)))))
   ((equal kind :tree)
    (and
     (pfm-tree-node-shape-p object)
     (pfm-well-formed-p
      :tree-list
      (pfm-tree-children object))))
   ((equal kind :tree-list)
    (if (consp object)
        (and
         (pfm-well-formed-p :tree (car object))
         (pfm-well-formed-p :tree-list (cdr object)))
      (equal object nil)))
   (t nil)))

(defun pfm-raw-heap-p (heap)
  (pfm-well-formed-p :raw-heap heap))

(defun pfm-tree-p (tree)
  (pfm-well-formed-p :tree tree))

(defun pfm-tree-list-p (trees)
  (pfm-well-formed-p :tree-list trees))

;; SIZE-HEAP, SIZE-TREE, and SIZE-LIST are represented by one exact
;; kind-indexed recursion over the corresponding source datatype.

(defun pfm-size-of (kind object)
  (declare (xargs :measure (acl2-count object)))
  (cond
   ((equal kind :raw-heap)
    (if (equal object nil)
        0
      (if (pfm-heap-node-shape-p object)
          (pfm-size-of :tree (pfm-heap-tree object))
        0)))
   ((equal kind :tree)
    (if (pfm-tree-node-shape-p object)
        (+
         1
         (pfm-size-of
          :tree-list
          (pfm-tree-children object)))
      0))
   ((equal kind :tree-list)
    (if (consp object)
        (+
         (pfm-size-of :tree (car object))
         (pfm-size-of :tree-list (cdr object)))
      0))
   (t 0)))

(defun pfm-size-heap (heap)
  (pfm-size-of :raw-heap heap))

;; LE-ROOTS and the mutually recursive heap predicates retain the exact
;; pairing-heap invariant carried by every value of the source HEAP record.

(defun pfm-le-tree-p (element tree)
  (and
   (pfm-tree-node-shape-p tree)
   (pfm-le-p element
             (pfm-tree-element tree))))

(defun pfm-le-roots-p (element trees)
  (declare (xargs :measure (acl2-count trees)))
  (if (consp trees)
      (and
       (pfm-le-tree-p element (car trees))
       (pfm-le-roots-p element (cdr trees)))
    (equal trees nil)))

(defun pfm-heap-structure-p (kind object)
  (declare (xargs :measure (acl2-count object)))
  (cond
   ((equal kind :raw-heap)
    (if (equal object nil)
        t
      (and
       (pfm-heap-node-shape-p object)
       (pfm-heap-structure-p
        :tree
        (pfm-heap-tree object)))))
   ((equal kind :tree)
    (and
     (pfm-tree-node-shape-p object)
     (pfm-le-roots-p
      (pfm-tree-element object)
      (pfm-tree-children object))
     (pfm-heap-structure-p
      :tree-list
      (pfm-tree-children object))))
   ((equal kind :tree-list)
    (if (consp object)
        (and
         (pfm-heap-structure-p :tree (car object))
         (pfm-heap-structure-p
          :tree-list
          (cdr object)))
      (equal object nil)))
   (t nil)))

(defun pfm-heap-p (heap)
  (pfm-heap-structure-p :raw-heap heap))

;; The source record HEAP has only its raw-heap field and invariant, so
;; quantifying below over exactly the well-formed raw heaps satisfying
;; PFM-HEAP-P is a bijective proof-erasing representation of that record.

;; MINIMUM-TREE and MINIMUM are arbitrary except for their exact source
;; equations on tree roots and nonempty raw heaps.

(defstub pfm-minimum-tree (tree) t)
(defstub pfm-minimum (heap) t)

(defun-sk pfm-minimum-tree-law-p ()
  (forall (element children)
    (implies
     (pfm-tree-list-p children)
     (equal
      (pfm-minimum-tree
       (pfm-tree-node element children))
      element))))

(defun-sk pfm-minimum-law-p ()
  (forall (tree)
    (implies
     (pfm-tree-p tree)
     (equal
      (pfm-minimum (pfm-heap-node tree))
      (pfm-minimum-tree tree)))))

;; These predicates are the two source match expressions after binding O1 to
;; the raw heap. The root remains internal to the constructor representation.

(defun pfm-match-success-p (heap)
  (if (equal heap nil)
      nil
    (and
     (pfm-heap-node-shape-p heap)
     (pfm-tree-node-shape-p
      (pfm-heap-tree heap)))))

(defun pfm-result-premise-p (heap result)
  (if (equal heap nil)
      nil
    (and
     (pfm-heap-node-shape-p heap)
     (pfm-tree-node-shape-p
      (pfm-heap-tree heap))
     (equal
      result
      (pfm-tree-element
       (pfm-heap-tree heap))))))

(defun-sk pfm-all-results-p (heap)
  (forall (result)
    (implies
     (pfm-result-premise-p heap result)
     (equal result (pfm-minimum heap)))))

(defun-sk
  ntp4vc-pearl-pairing-heap-pairingheap-find-minqtvc-statement
  ()
  (forall (heap)
    (implies
     (and
      (pfm-order-laws-p)
      (pfm-minimum-tree-law-p)
      (pfm-minimum-law-p)
      (pfm-raw-heap-p heap)
      (pfm-heap-p heap)
      (< 0 (pfm-size-heap heap)))
     (and
      (pfm-match-success-p heap)
      (pfm-all-results-p heap)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
