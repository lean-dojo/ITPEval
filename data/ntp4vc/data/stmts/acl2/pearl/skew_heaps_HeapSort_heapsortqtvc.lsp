;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/skew_heaps_HeapSort_heapsortqtvc: the skew-heap heapsort verification
;; condition, preserving heap size and multiplicities while building the heap,
;; then producing a sorted permutation while repeatedly removing its minimum.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; The source element type is represented by ACL2's full object universe.
;; LE remains an arbitrary relation; its total-preorder laws are explicit.

(defstub shs-le-op (left right) t)

(defun shs-le-p (left right)
  (if (shs-le-op left right) t nil))

(defun-sk shs-le-reflexive-p ()
  (forall (element)
    (shs-le-p element element)))

(defun-sk shs-le-transitive-p ()
  (forall (left middle right)
    (implies
     (and
      (shs-le-p left middle)
      (shs-le-p middle right))
     (shs-le-p left right))))

(defun-sk shs-le-total-p ()
  (forall (left right)
    (or
     (shs-le-p left right)
     (shs-le-p right left))))

(defun shs-order-laws-p ()
  (and
   (shs-le-reflexive-p)
   (shs-le-transitive-p)
   (shs-le-total-p)))

;; Empty trees are NIL. Nodes are exact records
;; (:SKEW-NODE left element right), matching the source binary-tree datatype.

(defun shs-node (left element right)
  (list :skew-node left element right))

(defun shs-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :skew-node)))

(defun shs-tree-left (tree)
  (cadr tree))

(defun shs-tree-element (tree)
  (caddr tree))

(defun shs-tree-right (tree)
  (cadddr tree))

(defun shs-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (shs-node-shape-p tree)
     (shs-tree-p (shs-tree-left tree))
     (shs-tree-p (shs-tree-right tree)))))

(defun shs-tree-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (shs-node-shape-p tree)
        (+
         1
         (shs-tree-size (shs-tree-left tree))
         (shs-tree-size (shs-tree-right tree)))
      0)))

(defun shs-tree-occ (element tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (shs-node-shape-p tree)
        (+
         (if (equal element (shs-tree-element tree)) 1 0)
         (shs-tree-occ element (shs-tree-left tree))
         (shs-tree-occ element (shs-tree-right tree)))
      0)))

(defun shs-tree-mem-p (element tree)
  (< 0 (shs-tree-occ element tree)))

(defun shs-le-root-p (element tree)
  (if (equal tree nil)
      t
    (if (shs-node-shape-p tree)
        (shs-le-p element (shs-tree-element tree))
      nil)))

(defun shs-heap-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (if (shs-node-shape-p tree)
        (let ((left (shs-tree-left tree))
              (element (shs-tree-element tree))
              (right (shs-tree-right tree)))
          (and
           (shs-le-root-p element left)
           (shs-heap-p left)
           (shs-le-root-p element right)
           (shs-heap-p right)))
      nil)))

;; MINIMUM is unconstrained on the empty tree and is exactly the root on every
;; node, as in the source SkewHeaps theory.

(defstub shs-minimum (tree) t)

(defun-sk shs-minimum-law-p ()
  (forall (left element right)
    (implies
     (and
      (shs-tree-p left)
      (shs-tree-p right))
     (equal
      (shs-minimum (shs-node left element right))
      element))))

;; Finite true lists directly represent source arrays. Total integer lookup
;; returns the fixed inhabitant NIL for every negative or out-of-range index;
;; every semantically relevant source access is in bounds.

(defun shs-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun shs-nth-int (index xs)
  (if (and
       (integerp index)
       (<= 0 index))
      (nth index xs)
    nil))

;; Source List.set leaves the list unchanged when its natural index is out of
;; bounds, unlike ACL2's UPDATE-NTH.

(defun shs-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (shs-list-set (cdr xs) (- index 1) value)))))

;; Exact occurrence count over the half-open mathematical integer interval
;; [LOWER, UPPER).

(defun shs-map-occ (value xs lower upper)
  (declare (xargs :measure (nfix (- upper lower))))
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (let ((last (- upper 1)))
        (+
         (if (equal (shs-nth-int last xs) value) 1 0)
         (shs-map-occ value xs lower last)))
    0))

(defun shs-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (shs-remove-first value (cdr xs))))))

;; Deletion-based multiset equality is exactly finite-list permutation.

(defun shs-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (shs-permutation-p
      (cdr left)
      (shs-remove-first (car left) right)))))

(defun-sk shs-sorted-sub-p (xs lower upper)
  (forall (i1 i2)
    (implies
     (and
      (integerp i1)
      (integerp i2)
      (<= lower i1)
      (< i1 i2)
      (< i2 upper))
     (shs-le-p
      (shs-nth-int i1 xs)
      (shs-nth-int i2 xs)))))

(defun shs-sorted-p (xs)
  (shs-sorted-sub-p xs 0 (len xs)))

(defun-sk shs-other-occurrences-p
    (before after distinguished)
  (forall (element)
    (implies
     (not (equal element distinguished))
     (equal
      (shs-tree-occ element after)
      (shs-tree-occ element before)))))

(defun-sk shs-occurrence-balance-p
    (current lower upper tree original original-upper)
  (forall (element)
    (equal
     (+
      (shs-map-occ element current lower upper)
      (shs-tree-occ element tree))
     (shs-map-occ element original 0 original-upper))))

(defun-sk shs-prefix-below-tree-p (xs upper tree)
  (forall (index element)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index upper)
      (shs-tree-mem-p element tree))
     (shs-le-p (shs-nth-int index xs) element))))

;; Extensional equality between the source list update's total integer-indexed
;; view and Function.update.

(defun-sk shs-list-set-map-equal-p (xs index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (shs-nth-int
       argument
       (shs-list-set xs (shs-int-to-nat index) value))
      (if (equal argument index)
          value
        (shs-nth-int argument xs))))))

;; First-loop insertion continuation.

(defun-sk shs-all-add-results-p
    (array n tree inserted)
  (forall (result)
    (implies
     (and
      (shs-tree-p result)
      (shs-heap-p result)
      (equal
       (shs-tree-occ inserted result)
       (+ (shs-tree-occ inserted tree) 1))
      (shs-other-occurrences-p tree result inserted)
      (equal
       (shs-tree-size result)
       (+ (shs-tree-size tree) 1)))
     (and
      (shs-heap-p result)
      (equal
       (shs-tree-size result)
       (+ (shs-tree-size tree) 1))
      (shs-occurrence-balance-p
       array
       (+ (shs-tree-size tree) 1)
       n
       result
       array
       n)))))

(defun shs-build-step-p (array n o1 tree)
  (implies
   (and
    (<= 0 (shs-tree-size tree))
    (<= (shs-tree-size tree) o1)
    (shs-heap-p tree)
    (shs-occurrence-balance-p
     array (shs-tree-size tree) n tree array n))
   (and
    (<= 0 (shs-tree-size tree))
    (< (shs-tree-size tree) (len array))
    (let ((inserted
           (shs-nth-int (shs-tree-size tree) array)))
      (and
       (shs-heap-p tree)
       (shs-all-add-results-p
        array n tree inserted))))))

;; Second-loop removal continuation.

(defun-sk shs-all-remove-results-p
    (original n before updated next-index)
  (forall (after)
    (implies
     (and
      (shs-tree-p after)
      (shs-heap-p after)
      (equal
       (shs-tree-occ (shs-minimum before) after)
       (- (shs-tree-occ (shs-minimum before) before) 1))
      (shs-other-occurrences-p
       before after (shs-minimum before))
      (equal
       (shs-tree-size after)
       (- (shs-tree-size before) 1)))
     (and
      (shs-sorted-sub-p updated 0 next-index)
      (shs-heap-p after)
      (equal
       (shs-tree-size after)
       (- n next-index))
      (shs-prefix-below-tree-p
       updated next-index after)
      (shs-occurrence-balance-p
       updated 0 next-index after original n)))))

(defun shs-extract-step-p
    (original n o2 tree array index)
  (implies
   (and
    (<= 0 index)
    (<= index o2)
    (shs-sorted-sub-p array 0 index)
    (shs-heap-p tree)
    (equal (shs-tree-size tree) (- n index))
    (shs-prefix-below-tree-p array index tree)
    (shs-occurrence-balance-p
     array 0 index tree original n))
   (and
    (shs-heap-p tree)
    (< 0 (shs-tree-size tree))
    (let* ((minimum (shs-minimum tree))
           (updated
            (shs-list-set
             array
             (shs-int-to-nat index)
             minimum)))
      (and
       (<= 0 index)
       (< index (len array))
       (implies
        (equal (len updated) (len array))
        (implies
         (shs-list-set-map-equal-p
          array index minimum)
         (and
          (shs-heap-p tree)
          (< 0 (shs-tree-size tree))
          (shs-all-remove-results-p
           original n tree updated (+ index 1))))))))))

(defun-sk shs-all-extract-indices-p
    (original n o2 tree array)
  (forall (index)
    (implies
     (integerp index)
     (shs-extract-step-p
      original n o2 tree array index))))

(defun shs-extract-exit-p
    (original n o2 tree array)
  (implies
   (and
    (shs-sorted-sub-p array 0 (+ o2 1))
    (shs-heap-p tree)
    (equal
     (shs-tree-size tree)
     (- n (+ o2 1)))
    (shs-prefix-below-tree-p
     array (+ o2 1) tree)
    (shs-occurrence-balance-p
     array 0 (+ o2 1) tree original n))
   (and
    (shs-sorted-p array)
    (shs-permutation-p original array))))

(defun-sk shs-all-extract-states-p (original n o2)
  (forall (tree array)
    (implies
     (and
      (shs-tree-p tree)
      (true-listp array))
     (implies
      (equal (len array) (len original))
      (and
       (shs-all-extract-indices-p
        original n o2 tree array)
       (shs-extract-exit-p
        original n o2 tree array))))))

(defun shs-extract-phase-p (original initial-tree n)
  (let ((o2 (- n 1)))
    (and
     (implies
      (<= 0 (+ o2 1))
      (and
       (shs-sorted-sub-p original 0 0)
       (shs-heap-p initial-tree)
       (equal (shs-tree-size initial-tree) (- n 0))
       (shs-prefix-below-tree-p original 0 initial-tree)
       (shs-occurrence-balance-p
        original 0 0 initial-tree original n)
       (shs-all-extract-states-p original n o2)))
     (implies
      (< (+ o2 1) 0)
      (and
       (shs-sorted-p original)
       (shs-permutation-p original original))))))

(defun shs-build-exit-p (array n o1 tree)
  (implies
   (and
    (shs-heap-p tree)
    (equal (shs-tree-size tree) (+ o1 1))
    (shs-occurrence-balance-p
     array (+ o1 1) n tree array n))
   (shs-extract-phase-p array tree n)))

(defun-sk shs-all-build-states-p (array n o1)
  (forall (tree)
    (implies
     (shs-tree-p tree)
     (and
      (shs-build-step-p array n o1 tree)
      (shs-build-exit-p array n o1 tree)))))

(defun shs-heapsort-vc-p (array)
  (let* ((n (len array))
         (o1 (- n 1)))
    (and
     (implies
      (<= 0 (+ o1 1))
      (and
       (shs-heap-p nil)
       (equal (shs-tree-size nil) 0)
       (shs-occurrence-balance-p
        array 0 n nil array n)
       (shs-all-build-states-p array n o1)))
     (implies
      (< (+ o1 1) 0)
      (shs-extract-phase-p array nil n)))))

(defun-sk
  ntp4vc-pearl-skew-heaps-heapsort-heapsortqtvc-statement
  ()
  (forall (array)
    (implies
     (true-listp array)
     (implies
      (and
       (shs-order-laws-p)
       (shs-minimum-law-p))
      (shs-heapsort-vc-p array)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
