;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sumrange_CumulativeTree_update_aux_complexityqtvc: the cumulative-tree
;; update verification condition, including the depth-bounded credit change,
;; updated range sums, and recursive continuation obligations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite integer lists represent Why3 arrays of mathematical integers.

(defun ct-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ct-integer-list-p (cdr xs)))))

;; Int.toNat sends negative integers to zero, and the exported total lookup
;; returns the integer default zero outside the list.

(defun ct-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ct-nth-int (index xs)
  (let ((value
         (nth
          (ct-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; Lean List.set and Isabelle list_update leave the list unchanged when the
;; natural-number index is out of bounds.

(defun ct-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (ct-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; This is the source ArraySum.sum recursion on the half-open interval
;; [LOWER, UPPER).

(defun ct-range-sum (xs lower upper)
  (declare
   (xargs :measure
          (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (ct-nth-int lower xs)
     (ct-range-sum xs (+ lower 1) upper))))

;; ComputerDivision.div truncates the integer quotient toward zero.

(defun ct-tdiv (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor
              (abs numerator)
              (abs denominator))))
        (if (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

;; Index records are exact triples (:CT-INDEXES low high sum).

(defun ct-indexes (low high isum)
  (list :ct-indexes low high isum))

(defun ct-indexes-shape-p (ind)
  (and
   (true-listp ind)
   (equal (len ind) 4)
   (equal (car ind) :ct-indexes)))

(defun ct-indexes-p (ind)
  (and
   (ct-indexes-shape-p ind)
   (integerp (cadr ind))
   (integerp (caddr ind))
   (integerp (cadddr ind))))

(defun ct-low (ind)
  (cadr ind))

(defun ct-high (ind)
  (caddr ind))

(defun ct-isum (ind)
  (cadddr ind))

;; Leaves and nodes are exact finite inductive-tree records.

(defun ct-leaf (ind)
  (list :ct-leaf ind))

(defun ct-node (ind left right)
  (list :ct-node ind left right))

(defun ct-leaf-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 2)
   (equal (car tree) :ct-leaf)))

(defun ct-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :ct-node)))

(defun ct-tree-indexes (tree)
  (cadr tree))

(defun ct-tree-left (tree)
  (caddr tree))

(defun ct-tree-right (tree)
  (cadddr tree))

(defun ct-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((ct-leaf-shape-p tree)
    (ct-indexes-p (ct-tree-indexes tree)))
   ((ct-node-shape-p tree)
    (and
     (ct-indexes-p (ct-tree-indexes tree))
     (ct-tree-p (ct-tree-left tree))
     (ct-tree-p (ct-tree-right tree))))
   (t nil)))

;; These are the source predicates is_indexes_for and is_tree_for.

(defun ct-is-indexes-for-p (ind a lower upper)
  (and
   (ct-indexes-p ind)
   (ct-integer-list-p a)
   (integerp lower)
   (integerp upper)
   (equal (ct-low ind) lower)
   (equal (ct-high ind) upper)
   (<= 0 lower)
   (< lower upper)
   (<= upper (len a))
   (equal
    (ct-isum ind)
    (ct-range-sum a lower upper))))

(defun ct-is-tree-for-p (tree a lower upper)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((ct-leaf-shape-p tree)
    (and
     (ct-is-indexes-for-p
      (ct-tree-indexes tree)
      a lower upper)
     (equal upper (+ lower 1))))
   ((ct-node-shape-p tree)
    (let* ((ind (ct-tree-indexes tree))
           (left (ct-tree-left tree))
           (right (ct-tree-right tree))
           (middle
            (ct-high (ct-tree-indexes left))))
      (and
       (ct-is-indexes-for-p ind a lower upper)
       (equal
        lower
        (ct-low (ct-tree-indexes left)))
       (equal
        upper
        (ct-high (ct-tree-indexes right)))
       (equal
        middle
        (ct-low (ct-tree-indexes right)))
       (< lower middle)
       (< middle upper)
       (equal
        middle
        (ct-tdiv (+ lower upper) 2))
       (ct-is-tree-for-p left a lower middle)
       (ct-is-tree-for-p right a middle upper))))
   (t nil)))

(defun ct-depth (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((ct-leaf-shape-p tree)
    1)
   ((ct-node-shape-p tree)
    (+
     1
     (max
      (ct-depth (ct-tree-left tree))
      (ct-depth (ct-tree-right tree)))))
   (t 0)))

;; This preserves the repeated source match asserting that the selected
;; recursive argument is one of the current node's two children.

(defun ct-child-p (tree child)
  (and
   (ct-node-shape-p tree)
   (or
    (equal (ct-tree-left tree) child)
    (equal (ct-tree-right tree) child))))

(defun ct-updated-indexes (ind a i v)
  (ct-indexes
   (ct-low ind)
   (ct-high ind)
   (+
    (ct-isum ind)
    (- v (ct-nth-int i a)))))

;; The common conclusion after rebuilding a node with the recursively updated
;; child retains the credit bound, root interval, and full updated-tree
;; invariant.

(defun ct-rebuilt-conclusion-p
    (original rebuilt a i v c c1)
  (and
   (<=
    (- c1 c)
    (ct-depth original))
   (equal
    (ct-low (ct-tree-indexes rebuilt))
    (ct-low (ct-tree-indexes original)))
   (equal
    (ct-high (ct-tree-indexes rebuilt))
    (ct-high (ct-tree-indexes original)))
   (ct-is-tree-for-p
    rebuilt
    (ct-list-set a (ct-int-to-nat i) v)
    (ct-low (ct-tree-indexes rebuilt))
    (ct-high (ct-tree-indexes rebuilt)))))

;; c1 and the replacement subtree remain universally quantified inside the
;; corresponding recursive continuation, exactly as in the source VC.

(defun-sk ct-left-continuation-p
    (original a i v c ind left right)
  (forall (c1 new-left)
    (implies
     (and
      (integerp c1)
      (ct-tree-p new-left))
     (implies
      (and
       (<=
        (- c1 (+ c 1))
        (ct-depth left))
       (equal
        (ct-low (ct-tree-indexes new-left))
        (ct-low (ct-tree-indexes left)))
       (equal
        (ct-high (ct-tree-indexes new-left))
        (ct-high (ct-tree-indexes left)))
       (ct-is-tree-for-p
        new-left
        (ct-list-set a (ct-int-to-nat i) v)
        (ct-low (ct-tree-indexes new-left))
        (ct-high (ct-tree-indexes new-left))))
      (ct-rebuilt-conclusion-p
       original
       (ct-node
        (ct-updated-indexes ind a i v)
        new-left
        right)
       a i v c c1)))))

(defun-sk ct-right-continuation-p
    (original a i v c ind left right)
  (forall (c1 new-right)
    (implies
     (and
      (integerp c1)
      (ct-tree-p new-right))
     (implies
      (and
       (<=
        (- c1 (+ c 1))
        (ct-depth right))
       (equal
        (ct-low (ct-tree-indexes new-right))
        (ct-low (ct-tree-indexes right)))
       (equal
        (ct-high (ct-tree-indexes new-right))
        (ct-high (ct-tree-indexes right)))
       (ct-is-tree-for-p
        new-right
        (ct-list-set a (ct-int-to-nat i) v)
        (ct-low (ct-tree-indexes new-right))
        (ct-high (ct-tree-indexes new-right))))
      (ct-rebuilt-conclusion-p
       original
       (ct-node
        (ct-updated-indexes ind a i v)
        left
        new-right)
       a i v c c1)))))

(defun ct-leaf-conclusion-p (tree ind a i v c)
  (let ((updated
         (ct-leaf
          (ct-indexes
           (ct-low ind)
           (ct-high ind)
           v))))
    (and
     (<=
      (- (+ c 1) c)
      (ct-depth tree))
     (equal
      (- v (ct-isum ind))
      (- v (ct-nth-int i a)))
     (equal
      (ct-low (ct-tree-indexes updated))
      (ct-low (ct-tree-indexes tree)))
     (equal
      (ct-high (ct-tree-indexes updated))
      (ct-high (ct-tree-indexes tree)))
     (ct-is-tree-for-p
      updated
      (ct-list-set a (ct-int-to-nat i) v)
      (ct-low (ct-tree-indexes updated))
      (ct-high (ct-tree-indexes updated))))))

(defun ct-node-conclusion-p
    (tree ind left right a i v c)
  (if (< i (ct-high (ct-tree-indexes left)))
      (and
       (ct-child-p tree left)
       (ct-is-tree-for-p
        left a
        (ct-low (ct-tree-indexes left))
        (ct-high (ct-tree-indexes left)))
       (<=
        (ct-low (ct-tree-indexes left))
        i)
       (<
        i
        (ct-high (ct-tree-indexes left)))
       (ct-left-continuation-p
        tree a i v c ind left right))
    (and
     (ct-child-p tree right)
     (ct-is-tree-for-p
      right a
      (ct-low (ct-tree-indexes right))
      (ct-high (ct-tree-indexes right)))
     (<=
      (ct-low (ct-tree-indexes right))
      i)
     (<
      i
      (ct-high (ct-tree-indexes right)))
     (ct-right-continuation-p
      tree a i v c ind left right))))

;; The arguments are the universally quantified typed parameters of the
;; source theorem; its three named assumptions form the antecedent.

(defun
  ntp4vc-pearl-sumrange-cumulativetree-update-aux-complexityqtvc-statement
  (tree a i v c)
  (implies
   (and
    (ct-tree-p tree)
    (ct-integer-list-p a)
    (integerp i)
    (integerp v)
    (integerp c)
    (ct-is-tree-for-p
     tree a
     (ct-low (ct-tree-indexes tree))
     (ct-high (ct-tree-indexes tree)))
    (<=
     (ct-low (ct-tree-indexes tree))
     i)
    (<
     i
     (ct-high (ct-tree-indexes tree))))
   (cond
    ((ct-leaf-shape-p tree)
     (ct-leaf-conclusion-p
      tree
      (ct-tree-indexes tree)
      a i v c))
    ((ct-node-shape-p tree)
     (ct-node-conclusion-p
      tree
      (ct-tree-indexes tree)
      (ct-tree-left tree)
      (ct-tree-right tree)
      a i v c))
    (t nil))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
