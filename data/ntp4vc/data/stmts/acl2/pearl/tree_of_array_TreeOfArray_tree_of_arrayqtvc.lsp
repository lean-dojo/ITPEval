;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/tree_of_array_TreeOfArray_tree_of_arrayqtvc: the full-array binary
;; tree construction verification condition, preserving inorder traversal
;; and the power-of-two height bounds on nonempty results. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite lists represent Why3 arrays. Their elements, and all tree
;; labels below, range over ACL2's full object universe, preserving the
;; source's arbitrary polymorphic element type.

(defun toa-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (toa-list-p (cdr xs))
    (equal xs nil)))

;; Empty trees are NIL. Nodes are exact tagged constructor records
;; (:TREE-OF-ARRAY-NODE left value right).

(defun toa-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :tree-of-array-node)))

(defun toa-tree-left (tree)
  (cadr tree))

(defun toa-tree-value (tree)
  (caddr tree))

(defun toa-tree-right (tree)
  (cadddr tree))

(defun toa-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (toa-node-shape-p tree)
     (toa-tree-p (toa-tree-left tree))
     (toa-tree-p (toa-tree-right tree)))))

(defun toa-tree-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (toa-node-shape-p tree)
        (+
         1
         (toa-tree-size (toa-tree-left tree))
         (toa-tree-size (toa-tree-right tree)))
      0)))

(defun toa-int-max (left right)
  (if (<= left right)
      right
    left))

(defun toa-tree-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (toa-node-shape-p tree)
        (+
         1
         (toa-int-max
          (toa-tree-height (toa-tree-left tree))
          (toa-tree-height (toa-tree-right tree))))
      0)))

(defun toa-tree-inorder (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      nil
    (if (toa-node-shape-p tree)
        (append
         (toa-tree-inorder (toa-tree-left tree))
         (cons
          (toa-tree-value tree)
          (toa-tree-inorder (toa-tree-right tree))))
      nil)))

;; These are the exported Int.toNat, List.take, and List.drop operations.

(defun toa-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun toa-list-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp xs))
      nil
    (cons
     (car xs)
     (toa-list-take (- count 1) (cdr xs)))))

(defun toa-list-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (endp xs))
      xs
    (toa-list-drop (- count 1) (cdr xs))))

(defun toa-height-bound-p (tree size)
  (let ((height (toa-tree-height tree)))
    (and
     (<= (expt 2 (- height 1)) size)
     (< size (expt 2 height)))))

;; RESULT retains its source universal quantifier over every finite binary
;; tree. The premise is exactly the contract of tree_of_array_aux at
;; [0,O1), and the conclusion is the wrapper's two postconditions.

(defun-sk toa-all-results-p (array o1)
  (forall (result)
    (implies
     (toa-tree-p result)
     (let ((n (- o1 0)))
       (implies
        (and
         (equal (toa-tree-size result) n)
         (equal
          (toa-tree-inorder result)
          (toa-list-drop
           0
           (toa-list-take
            (- (toa-int-to-nat o1) 0)
            array)))
         (implies
          (< 0 n)
          (toa-height-bound-p result n)))
        (and
         (equal
          (toa-tree-inorder result)
          (toa-list-drop
           0
           (toa-list-take
            (- (len array) 0)
            array)))
         (implies
          (< 0 (toa-tree-size result))
          (toa-height-bound-p
           result
           (toa-tree-size result)))))))))

;; ARRAY is the source theorem's universally quantified finite polymorphic
;; array. O1 remains the local binding for its mathematical-integer length.

(defun
  ntp4vc-pearl-tree-of-array-treeofarray-tree-of-arrayqtvc-statement
  (array)
  (implies
   (toa-list-p array)
   (let ((o1 (len array)))
     (and
      (and
       (<= 0 0)
       (<= 0 o1)
       (<= o1 (len array)))
      (toa-all-results-p array o1)))))

(value-triple :itpeval-statement-checked)
:q
