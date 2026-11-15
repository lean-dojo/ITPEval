;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/leftist_heap_LeftistHeap_delete_minqtvc: the delete-min verification
;; condition for a nonempty leftist heap, preserving child invariants, tree
;; size, and element occurrences after removal. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; The source element type is represented by ACL2's full object universe.
;; This conservative interface supplies its arbitrary order relation; the
;; reflexivity, transitivity, and totality laws remain explicit premises.

(defstub lhdm-le-op (left right) t)

(defun lhdm-le-p (left right)
  (if (lhdm-le-op left right) t nil))

(defun-sk lhdm-reflexive-p ()
  (forall (element)
    (lhdm-le-p element element)))

(defun-sk lhdm-transitive-p ()
  (forall (left middle right)
    (implies
     (and
      (lhdm-le-p left middle)
      (lhdm-le-p middle right))
     (lhdm-le-p left right))))

(defun-sk lhdm-total-p ()
  (forall (left right)
    (or
     (lhdm-le-p left right)
     (lhdm-le-p right left))))

(defun lhdm-order-laws-p ()
  (and
   (lhdm-reflexive-p)
   (lhdm-transitive-p)
   (lhdm-total-p)))

;; Empty trees are NIL. Nodes are exact records
;; (:LEFTIST-NODE rank left element right), preserving the source's finite
;; inductive tree domain and its integer rank annotation.

(defun lhdm-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 5)
   (equal (car tree) :leftist-node)))

(defun lhdm-tree-rank-field (tree)
  (cadr tree))

(defun lhdm-tree-left (tree)
  (caddr tree))

(defun lhdm-tree-element (tree)
  (cadddr tree))

(defun lhdm-tree-right (tree)
  (car (cddddr tree)))

(defun lhdm-node (rank left element right)
  (list :leftist-node rank left element right))

(defun lhdm-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (lhdm-node-shape-p tree)
     (integerp (lhdm-tree-rank-field tree))
     (lhdm-tree-p (lhdm-tree-left tree))
     (lhdm-tree-p (lhdm-tree-right tree)))))

(defun lhdm-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (lhdm-node-shape-p tree)
        (+
         1
         (lhdm-size (lhdm-tree-left tree))
         (lhdm-size (lhdm-tree-right tree)))
      0)))

(defun lhdm-occ (element tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (lhdm-node-shape-p tree)
        (+
         (if (equal element
                    (lhdm-tree-element tree))
             1
           0)
         (lhdm-occ element
                   (lhdm-tree-left tree))
         (lhdm-occ element
                   (lhdm-tree-right tree)))
      0)))

(defun lhdm-rank (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (lhdm-node-shape-p tree)
        (let ((left-rank
               (lhdm-rank (lhdm-tree-left tree)))
              (right-rank
               (lhdm-rank (lhdm-tree-right tree))))
          (+
           1
           (if (<= left-rank right-rank)
               left-rank
             right-rank)))
      0)))

(defun lhdm-le-root-p (element tree)
  (if (equal tree nil)
      t
    (if (lhdm-node-shape-p tree)
        (lhdm-le-p element
                   (lhdm-tree-element tree))
      nil)))

(defun lhdm-is-heap-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (lhdm-node-shape-p tree)
        (let ((left (lhdm-tree-left tree))
              (element (lhdm-tree-element tree))
              (right (lhdm-tree-right tree)))
          (and
           (lhdm-le-root-p element left)
           (lhdm-is-heap-p left)
           (lhdm-le-root-p element right)
           (lhdm-is-heap-p right)))
      nil)))

(defun lhdm-leftist-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (lhdm-node-shape-p tree)
        (let ((left (lhdm-tree-left tree))
              (right (lhdm-tree-right tree)))
          (and
           (equal
            (lhdm-tree-rank-field tree)
            (lhdm-rank tree))
           (lhdm-leftist-p left)
           (lhdm-leftist-p right)
           (<= (lhdm-rank right)
               (lhdm-rank left))))
      nil)))

(defun lhdm-leftist-heap-p (tree)
  (and
   (lhdm-is-heap-p tree)
   (lhdm-leftist-p tree)))

;; MINIMUM is arbitrary except for the exact source law saying that the
;; minimum of every node is its root element.

(defstub lhdm-minimum (tree) t)

(defun-sk lhdm-minimum-law-p ()
  (forall (rank left element right)
    (implies
     (and
      (integerp rank)
      (lhdm-tree-p left)
      (lhdm-tree-p right))
     (equal
      (lhdm-minimum
       (lhdm-node rank left element right))
      element))))

;; This is the first case expression in the theorem's conclusion.

(defun lhdm-child-heaps-p (tree)
  (if (equal tree nil)
      nil
    (if (lhdm-node-shape-p tree)
        (and
         (lhdm-leftist-heap-p
          (lhdm-tree-left tree))
         (lhdm-leftist-heap-p
          (lhdm-tree-right tree)))
      nil)))

;; Preserve the source universal equality of occurrence counts for every
;; element in a candidate result.

(defun-sk lhdm-combined-occurrences-p
    (result left right)
  (forall (element)
    (equal
     (lhdm-occ element result)
     (+
      (lhdm-occ element left)
      (lhdm-occ element right)))))

(defun lhdm-result-premise-p (tree result)
  (if (equal tree nil)
      nil
    (if (lhdm-node-shape-p tree)
        (let ((left (lhdm-tree-left tree))
              (right (lhdm-tree-right tree)))
          (and
           (equal
            (lhdm-size result)
            (+
             (lhdm-size left)
             (lhdm-size right)))
           (lhdm-combined-occurrences-p
            result left right)
           (lhdm-leftist-heap-p result)))
      nil)))

(defun-sk lhdm-other-occurrences-p
    (result tree minimum)
  (forall (element)
    (implies
     (not (equal element minimum))
     (equal
      (lhdm-occ element result)
      (lhdm-occ element tree)))))

(defun lhdm-result-postcondition-p (tree result)
  (let ((minimum (lhdm-minimum tree)))
    (and
     (equal
      (lhdm-occ minimum result)
      (- (lhdm-occ minimum tree) 1))
     (lhdm-other-occurrences-p
      result tree minimum)
     (equal
      (lhdm-size result)
      (- (lhdm-size tree) 1))
     (lhdm-leftist-heap-p result))))

;; RESULT remains universally quantified over the complete typed tree domain,
;; exactly inside the delete-min verification condition.

(defun-sk lhdm-all-results-p (tree)
  (forall (result)
    (implies
     (and
      (lhdm-tree-p result)
      (lhdm-result-premise-p tree result))
     (lhdm-result-postcondition-p tree result))))

(defun-sk
  ntp4vc-pearl-leftist-heap-leftistheap-delete-minqtvc-statement
  ()
  (forall (tree)
    (implies
     (and
      (lhdm-order-laws-p)
      (lhdm-minimum-law-p)
      (lhdm-tree-p tree)
      (< 0 (lhdm-size tree))
      (lhdm-leftist-heap-p tree))
     (and
      (lhdm-child-heaps-p tree)
      (lhdm-all-results-p tree)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
