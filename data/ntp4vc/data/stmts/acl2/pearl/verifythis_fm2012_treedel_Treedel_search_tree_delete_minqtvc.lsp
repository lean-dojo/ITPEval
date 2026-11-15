;; Statement-only formalization of the NTP4VC corpus artifact
;; pearl/verifythis_fm2012_treedel_Treedel_search_tree_delete_minqtvc:
;; the verification condition for deleting the minimum node from a
;; pointer-modeled binary tree, including tree/heap consistency, zipper
;; reconstruction, inorder uniqueness, and the functional memory update.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Locations and memories are arbitrary source-domain objects.  Memory lookup
;; is the exact total-function interface of Why3's map from locations to node
;; records; all source typing conditions remain explicit below.

(defstub tdm-loc-p (*) => *)
(defstub tdm-memory-p (*) => *)
(defstub tdm-null () => *)
(defstub tdm-memory-get (* *) => *)
(defstub tdm-eq-loc (* *) => *)

;; Exact records for the source Memory.node type.

(defun tdm-heap-node (left right data)
  (list :tdm-heap-node left right data))

(defun tdm-heap-node-p (node)
  (and
   (true-listp node)
   (equal (len node) 4)
   (equal (car node) :tdm-heap-node)
   (tdm-loc-p (cadr node))
   (tdm-loc-p (caddr node))
   (integerp (cadddr node))))

(defun tdm-heap-node-left (node)
  (cadr node))

(defun tdm-heap-node-right (node)
  (caddr node))

(defun tdm-heap-node-data (node)
  (cadddr node))

(defun-sk tdm-memory-interface-typed-p ()
  (forall (memory location)
    (implies
     (and
      (tdm-memory-p memory)
      (tdm-loc-p location))
     (tdm-heap-node-p
      (tdm-memory-get memory location)))))

(defun-sk tdm-eq-loc-interface-typed-p ()
  (forall (left right)
    (implies
     (and
      (tdm-loc-p left)
      (tdm-loc-p right))
     (booleanp (tdm-eq-loc left right)))))

;; Exact finite inductive binary trees over locations.

(defun tdm-tree-empty ()
  (list :tdm-tree-empty))

(defun tdm-tree-node (left location right)
  (list :tdm-tree-node left location right))

(defun tdm-tree-empty-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 1)
   (equal (car tree) :tdm-tree-empty)))

(defun tdm-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :tdm-tree-node)))

(defun tdm-tree-left (tree)
  (cadr tree))

(defun tdm-tree-location (tree)
  (caddr tree))

(defun tdm-tree-right (tree)
  (cadddr tree))

(defun tdm-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((tdm-tree-empty-p tree) t)
   ((tdm-tree-node-shape-p tree)
    (and
     (tdm-tree-p (tdm-tree-left tree))
     (tdm-loc-p (tdm-tree-location tree))
     (tdm-tree-p (tdm-tree-right tree))))
   (t nil)))

(defun tdm-root (tree)
  (if (tdm-tree-node-shape-p tree)
      (tdm-tree-location tree)
    (tdm-null)))

(defun tdm-inorder (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (tdm-tree-node-shape-p tree)
      (append
       (tdm-inorder (tdm-tree-left tree))
       (cons
        (tdm-tree-location tree)
        (tdm-inorder (tdm-tree-right tree))))
    nil))

(defun tdm-istree-p (memory tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((tdm-tree-empty-p tree) t)
   ((tdm-tree-node-shape-p tree)
    (let* ((left (tdm-tree-left tree))
           (location (tdm-tree-location tree))
           (right (tdm-tree-right tree))
           (node (tdm-memory-get memory location)))
      (and
       (not (equal location (tdm-null)))
       (tdm-istree-p memory left)
       (tdm-istree-p memory right)
       (equal (tdm-root left)
              (tdm-heap-node-left node))
       (equal (tdm-root right)
              (tdm-heap-node-right node)))))
   (t nil)))

(defun tdm-tree-left-is-p (tree candidate)
  (and
   (tdm-tree-node-shape-p tree)
   (equal candidate (tdm-tree-left tree))))

(defun tdm-tree-right-is-p (tree candidate)
  (and
   (tdm-tree-node-shape-p tree)
   (equal candidate (tdm-tree-right tree))))

(defun tdm-tree-child-is-p (tree candidate)
  (and
   (tdm-tree-node-shape-p tree)
   (or
    (equal (tdm-tree-left tree) candidate)
    (equal (tdm-tree-right tree) candidate))))

;; Exact finite inductive zippers for a left descent.

(defun tdm-zipper-top ()
  (list :tdm-zipper-top))

(defun tdm-zipper-left (zipper location right)
  (list :tdm-zipper-left zipper location right))

(defun tdm-zipper-top-p (zipper)
  (and
   (true-listp zipper)
   (equal (len zipper) 1)
   (equal (car zipper) :tdm-zipper-top)))

(defun tdm-zipper-left-shape-p (zipper)
  (and
   (true-listp zipper)
   (equal (len zipper) 4)
   (equal (car zipper) :tdm-zipper-left)))

(defun tdm-zipper-context (zipper)
  (cadr zipper))

(defun tdm-zipper-location (zipper)
  (caddr zipper))

(defun tdm-zipper-right (zipper)
  (cadddr zipper))

(defun tdm-zipper-p (zipper)
  (declare (xargs :measure (acl2-count zipper)))
  (cond
   ((tdm-zipper-top-p zipper) t)
   ((tdm-zipper-left-shape-p zipper)
    (and
     (tdm-zipper-p (tdm-zipper-context zipper))
     (tdm-loc-p (tdm-zipper-location zipper))
     (tdm-tree-p (tdm-zipper-right zipper))))
   (t nil)))

(defun tdm-zip (tree zipper)
  (declare (xargs :measure (acl2-count zipper)))
  (cond
   ((tdm-zipper-top-p zipper) tree)
   ((tdm-zipper-left-shape-p zipper)
    (tdm-zip
     (tdm-tree-node
      tree
      (tdm-zipper-location zipper)
      (tdm-zipper-right zipper))
     (tdm-zipper-context zipper)))
   (t tree)))

(defun tdm-inorderz (zipper)
  (declare (xargs :measure (acl2-count zipper)))
  (cond
   ((tdm-zipper-top-p zipper) nil)
   ((tdm-zipper-left-shape-p zipper)
    (append
     (cons
      (tdm-zipper-location zipper)
      (tdm-inorder (tdm-zipper-right zipper)))
     (tdm-inorderz (tdm-zipper-context zipper))))
   (t nil)))

;; The direct branch of the deletion, including the source match expressions
;; on the initial tree and its inorder traversal.

(defun tdm-direct-delete-branch-p (initial-tree memory)
  (if (tdm-tree-node-shape-p initial-tree)
      (let* ((right-tree (tdm-tree-right initial-tree))
             (root-location (tdm-root initial-tree))
             (items (tdm-inorder initial-tree)))
        (and
         (tdm-istree-p memory right-tree)
         (equal
          (tdm-root right-tree)
          (tdm-heap-node-right
           (tdm-memory-get memory root-location)))
         (consp items)
         (equal
          (tdm-heap-node-data
           (tdm-memory-get memory root-location))
          (tdm-heap-node-data
           (tdm-memory-get memory (car items))))
         (equal (tdm-inorder right-tree)
                (cdr items))))
    nil))

;; Pointwise predicates preserve the source's function equality and update
;; conditions over the complete location domain.

(defun-sk tdm-memory-unchanged-off-p
    (updated-memory original-memory changed-location)
  (forall (location)
    (implies
     (and
      (tdm-loc-p location)
      (not (equal location changed-location)))
     (equal
      (tdm-memory-get updated-memory location)
      (tdm-memory-get original-memory location)))))

(defun-sk tdm-all-data-unchanged-p
    (updated-memory original-memory)
  (forall (location)
    (implies
     (tdm-loc-p location)
     (equal
      (tdm-heap-node-data
       (tdm-memory-get updated-memory location))
      (tdm-heap-node-data
       (tdm-memory-get original-memory location))))))

(defun tdm-final-inorder-p
    (initial-tree original-memory updated-memory parent output-tree)
  (let ((items (tdm-inorder initial-tree)))
    (and
     (consp items)
     (equal
      (tdm-heap-node-data
       (tdm-memory-get
        original-memory
        (tdm-heap-node-left
         (tdm-memory-get original-memory parent))))
      (tdm-heap-node-data
       (tdm-memory-get updated-memory (car items))))
     (equal
      (tdm-inorder output-tree)
      (cdr items)))))

;; Quantifier helpers below follow the source nesting from the innermost
;; post-state outward.

(defun tdm-final-right-tree-body-p
    (initial-tree original-memory updated-memory subtree right-context
                  zipper parent left-subtree right-subtree)
  (declare (ignore left-subtree))
  (implies
   (tdm-tree-p right-subtree)
   (implies
    (tdm-tree-right-is-p subtree right-subtree)
    (let ((output-tree
           (tdm-zip
            right-subtree
            (tdm-zipper-left zipper parent right-context))))
      (and
       (tdm-all-data-unchanged-p
        updated-memory original-memory)
       (tdm-istree-p updated-memory output-tree)
       (equal (tdm-root output-tree)
              (tdm-root initial-tree))
       (tdm-final-inorder-p
        initial-tree original-memory updated-memory
        parent output-tree))))))

(defun-sk tdm-all-final-right-trees-p
    (initial-tree original-memory updated-memory subtree right-context
                  zipper parent left-subtree)
  (forall (right-subtree)
    (tdm-final-right-tree-body-p
     initial-tree original-memory updated-memory subtree right-context
     zipper parent left-subtree right-subtree)))

(defun tdm-final-left-tree-body-p
    (initial-tree original-memory updated-memory subtree right-context
                  zipper parent left-subtree)
  (implies
   (tdm-tree-p left-subtree)
   (implies
    (tdm-tree-left-is-p subtree left-subtree)
    (and
     (not (equal subtree (tdm-tree-empty)))
     (tdm-all-final-right-trees-p
      initial-tree original-memory updated-memory subtree right-context
      zipper parent left-subtree)))))

(defun-sk tdm-all-final-left-trees-p
    (initial-tree original-memory updated-memory subtree right-context
                  zipper parent)
  (forall (left-subtree)
    (tdm-final-left-tree-body-p
     initial-tree original-memory updated-memory subtree right-context
     zipper parent left-subtree)))

(defun tdm-updated-memory-body-p
    (initial-tree original-memory subtree right-context zipper parent
                  updated-memory)
  (implies
   (tdm-memory-p updated-memory)
   (let* ((old-parent-node
           (tdm-memory-get original-memory parent))
          (left-location
           (tdm-heap-node-left old-parent-node))
          (left-node
           (tdm-memory-get original-memory left-location))
          (new-parent-node
           (tdm-heap-node
            (tdm-heap-node-right left-node)
            (tdm-heap-node-right old-parent-node)
            (tdm-heap-node-data old-parent-node))))
     (implies
      (and
       (equal
        (tdm-memory-get updated-memory parent)
        new-parent-node)
       (tdm-memory-unchanged-off-p
        updated-memory original-memory parent))
      (and
       (not (equal subtree (tdm-tree-empty)))
       (tdm-all-final-left-trees-p
        initial-tree original-memory updated-memory subtree
        right-context zipper parent))))))

(defun-sk tdm-all-updated-memories-p
    (initial-tree original-memory subtree right-context zipper parent)
  (forall (updated-memory)
    (tdm-updated-memory-body-p
     initial-tree original-memory subtree right-context zipper parent
     updated-memory)))

(defun tdm-inner-false-branch-p
    (initial-tree memory subtree right-context zipper parent)
  (let ((parent-left
         (tdm-heap-node-left
          (tdm-memory-get memory parent))))
    (and
     (not (equal parent-left (tdm-null)))
     (not (equal parent-left (tdm-null)))
     (not (equal parent (tdm-null)))
     (tdm-all-updated-memories-p
      initial-tree memory subtree right-context zipper parent))))

(defun tdm-inner-left-tree-body-p
    (initial-tree memory subtree right-context zipper parent
                  right-subtree left-subtree)
  (implies
   (tdm-tree-p left-subtree)
   (implies
    (tdm-tree-left-is-p subtree left-subtree)
    (let* ((parent-left
            (tdm-heap-node-left
             (tdm-memory-get memory parent)))
           (nested-left
            (tdm-heap-node-left
             (tdm-memory-get memory parent-left)))
           (partial-tree
            (tdm-tree-node
             left-subtree parent-left right-subtree)))
      (and
       (not (equal nested-left (tdm-null)))
       (tdm-tree-child-is-p subtree left-subtree)
       (not (equal parent-left (tdm-null)))
       (not (equal nested-left (tdm-null)))
       (tdm-istree-p memory partial-tree)
       (equal
        (tdm-zip
         partial-tree
         (tdm-zipper-left zipper parent right-context))
        initial-tree))))))

(defun-sk tdm-all-inner-left-trees-p
    (initial-tree memory subtree right-context zipper parent
                  right-subtree)
  (forall (left-subtree)
    (tdm-inner-left-tree-body-p
     initial-tree memory subtree right-context zipper parent
     right-subtree left-subtree)))

(defun tdm-inner-right-tree-body-p
    (initial-tree memory subtree right-context zipper parent
                  right-subtree)
  (implies
   (tdm-tree-p right-subtree)
   (implies
    (tdm-tree-right-is-p subtree right-subtree)
    (and
     (not (equal subtree (tdm-tree-empty)))
     (tdm-all-inner-left-trees-p
      initial-tree memory subtree right-context zipper parent
      right-subtree)))))

(defun-sk tdm-all-inner-right-trees-p
    (initial-tree memory subtree right-context zipper parent)
  (forall (right-subtree)
    (tdm-inner-right-tree-body-p
     initial-tree memory subtree right-context zipper parent
     right-subtree)))

(defun tdm-inner-true-branch-p
    (initial-tree memory subtree right-context zipper parent)
  (and
   (not (equal subtree (tdm-tree-empty)))
   (tdm-all-inner-right-trees-p
    initial-tree memory subtree right-context zipper parent)))

(defun tdm-loop-state-body-p
    (initial-tree memory subtree right-context zipper parent)
  (implies
   (and
    (tdm-tree-p subtree)
    (tdm-tree-p right-context)
    (tdm-zipper-p zipper)
    (tdm-loc-p parent))
   (implies
    (and
     (not (equal parent (tdm-null)))
     (not
      (equal
       (tdm-heap-node-left
        (tdm-memory-get memory parent))
       (tdm-null)))
     (let ((partial-tree
            (tdm-tree-node subtree parent right-context)))
       (and
        (tdm-istree-p memory partial-tree)
        (equal
         (tdm-zip partial-tree zipper)
         initial-tree))))
    (let* ((parent-left
            (tdm-heap-node-left
             (tdm-memory-get memory parent)))
           (nested-left
            (tdm-heap-node-left
             (tdm-memory-get memory parent-left)))
           (o5 (tdm-null)))
      (implies
       (iff (tdm-eq-loc nested-left o5)
            (equal nested-left o5))
       (if (not (tdm-eq-loc nested-left o5))
           (tdm-inner-true-branch-p
            initial-tree memory subtree right-context zipper parent)
         (tdm-inner-false-branch-p
          initial-tree memory subtree right-context zipper parent)))))))

(defun-sk tdm-all-loop-states-p
    (initial-tree memory)
  (forall (subtree right-context zipper parent)
    (tdm-loop-state-body-p
     initial-tree memory subtree right-context zipper parent)))

(defun tdm-initial-left-tree-body-p
    (initial-tree memory o1 right-subtree left-subtree)
  (implies
   (tdm-tree-p left-subtree)
   (implies
    (tdm-tree-left-is-p initial-tree left-subtree)
    (let ((partial-tree
           (tdm-tree-node
            left-subtree
            (tdm-root initial-tree)
            right-subtree)))
      (and
       (not (equal (tdm-root initial-tree)
                   (tdm-null)))
       (equal
        (tdm-heap-node-left
         (tdm-memory-get memory
                         (tdm-root initial-tree)))
        o1)
       (not (equal o1 (tdm-null)))
       (tdm-istree-p memory partial-tree)
       (equal
        (tdm-zip partial-tree (tdm-zipper-top))
        initial-tree)
       (tdm-all-loop-states-p
        initial-tree memory))))))

(defun-sk tdm-all-initial-left-trees-p
    (initial-tree memory o1 right-subtree)
  (forall (left-subtree)
    (tdm-initial-left-tree-body-p
     initial-tree memory o1 right-subtree left-subtree)))

(defun tdm-initial-right-tree-body-p
    (initial-tree memory o1 right-subtree)
  (implies
   (tdm-tree-p right-subtree)
   (implies
    (tdm-tree-right-is-p initial-tree right-subtree)
    (and
     (not (equal initial-tree (tdm-tree-empty)))
     (tdm-all-initial-left-trees-p
      initial-tree memory o1 right-subtree)))))

(defun-sk tdm-all-initial-right-trees-p
    (initial-tree memory o1)
  (forall (right-subtree)
    (tdm-initial-right-tree-body-p
     initial-tree memory o1 right-subtree)))

(defun tdm-iterative-delete-branch-p
    (initial-tree memory o1)
  (and
   (not (equal o1 (tdm-null)))
   (not (equal initial-tree (tdm-tree-empty)))
   (tdm-all-initial-right-trees-p
    initial-tree memory o1)))

(defun tdm-postcondition-p (initial-tree memory)
  (let* ((root-location (tdm-root initial-tree))
         (o1
          (tdm-heap-node-left
           (tdm-memory-get memory root-location)))
         (o2 (tdm-null)))
    (and
     (not (equal root-location (tdm-null)))
     (implies
      (iff (tdm-eq-loc o1 o2)
           (equal o1 o2))
      (if (tdm-eq-loc o1 o2)
          (and
           (not (equal root-location (tdm-null)))
           (not (equal root-location (tdm-null)))
           (tdm-direct-delete-branch-p
            initial-tree memory))
        (tdm-iterative-delete-branch-p
         initial-tree memory o1))))))

(defun tdm-top-body-p (initial-tree memory)
  (implies
   (and
    (tdm-tree-p initial-tree)
    (tdm-memory-p memory))
   (implies
    (and
     (not (equal (tdm-root initial-tree)
                 (tdm-null)))
     (tdm-istree-p memory initial-tree)
     (no-duplicatesp-equal
      (tdm-inorder initial-tree)))
    (tdm-postcondition-p initial-tree memory))))

(defun-sk
  ntp4vc-pearl-verifythis-fm2012-treedel-treedel-search-tree-delete-minqtvc-statement
  ()
  (forall (initial-tree memory)
    (implies
     (and
      (tdm-loc-p (tdm-null))
      (tdm-memory-interface-typed-p)
      (tdm-eq-loc-interface-typed-p))
     (tdm-top-body-p initial-tree memory))))

(value-triple :itpeval-statement-checked)
:q
