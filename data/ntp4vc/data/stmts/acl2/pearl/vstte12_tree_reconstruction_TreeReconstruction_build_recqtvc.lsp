;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vstte12_tree_reconstruction_TreeReconstruction_build_recqtvc: the
;; recursive tree-reconstruction verification condition over integer
;; leaf-depth lists, including success, failure, and termination clauses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Finite binary trees are represented bijectively by the exact constructor
;; records (:TRBR-LEAF) and (:TRBR-NODE left-subtree right-subtree).

(defun trbr-leaf ()
  (list :trbr-leaf))

(defun trbr-node (left right)
  (list :trbr-node left right))

(defun trbr-leaf-shape-p (tree)
  (equal tree (trbr-leaf)))

(defun trbr-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 3)
   (equal (car tree) :trbr-node)))

(defun trbr-tree-left (tree)
  (cadr tree))

(defun trbr-tree-right (tree)
  (caddr tree))

(defun trbr-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((trbr-leaf-shape-p tree)
    t)
   ((trbr-node-shape-p tree)
    (and
     (trbr-tree-p (trbr-tree-left tree))
     (trbr-tree-p (trbr-tree-right tree))))
   (t nil)))

(defun trbr-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (trbr-integer-list-p (cdr xs)))
    (equal xs nil)))

;; This is the source Tree.depths function. Leaves contribute the current
;; mathematical-integer depth; nodes concatenate the left and right lists
;; after increasing the depth by one.

(defun trbr-depths (depth tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond
   ((trbr-leaf-shape-p tree)
    (list depth))
   ((trbr-node-shape-p tree)
    (append
     (trbr-depths (+ depth 1) (trbr-tree-left tree))
     (trbr-depths (+ depth 1) (trbr-tree-right tree))))
   (t nil)))

;; The exported source definitions make list head total with integer default
;; zero. On every nonempty list this is ordinary CAR.

(defun trbr-head (xs)
  (if (consp xs)
      (car xs)
    0))

;; No finite binary tree at DEPTH has a depth-list prefix of SEQUENCE.

(defun-sk trbr-no-prefix-tree-p (depth sequence)
  (forall (tree suffix)
    (implies
     (and
      (trbr-tree-p tree)
      (trbr-integer-list-p suffix))
     (not
      (equal
       (append (trbr-depths depth tree) suffix)
       sequence)))))

;; This is the continuation required after every possible successful right
;; recursive call.

(defun-sk trbr-all-right-results-p
    (sequence depth left suffix1)
  (forall (right suffix2)
    (implies
     (and
      (trbr-tree-p right)
      (trbr-integer-list-p suffix2))
     (implies
      (equal
       suffix1
       (append
        (trbr-depths (+ depth 1) right)
        suffix2))
      (equal
       sequence
       (append
        (trbr-depths
         depth
         (trbr-node left right))
        suffix2))))))

;; The body following one possible successful left recursive call preserves
;; the lexicographic variant, handles every possible right result, and
;; propagates right-recursion failure to the original call.

(defun trbr-left-continuation-p
    (sequence depth left suffix1)
  (and
   (or
    (and
     (<= 0 (len sequence))
     (< (len suffix1) (len sequence)))
    (and
     (equal (len sequence) (len suffix1))
     (<= 0 (- (trbr-head sequence) depth))
     (<
      (- (trbr-head suffix1) (+ depth 1))
      (- (trbr-head sequence) depth))))
   (trbr-all-right-results-p
    sequence depth left suffix1)
   (implies
    (trbr-no-prefix-tree-p (+ depth 1) suffix1)
    (trbr-no-prefix-tree-p depth sequence))))

;; Preserve the source universal quantification over every possible left
;; tree and remainder returned by the first recursive call.

(defun-sk trbr-all-left-results-p (sequence depth)
  (forall (left suffix1)
    (implies
     (and
      (trbr-tree-p left)
      (trbr-integer-list-p suffix1))
     (implies
      (equal
       sequence
       (append
        (trbr-depths (+ depth 1) left)
        suffix1))
      (trbr-left-continuation-p
       sequence depth left suffix1)))))

(defun
  ntp4vc-pearl-vstte12-tree-reconstruction-treereconstruction-build-recqtvc-statement
  (sequence depth)
  (implies
   (and
    (trbr-integer-list-p sequence)
    (integerp depth))
   (if (endp sequence)
       (trbr-no-prefix-tree-p depth sequence)
     (let ((head (car sequence))
           (tail (cdr sequence)))
       (if (< head depth)
           (trbr-no-prefix-tree-p depth sequence)
         (if (equal head depth)
             (equal
              sequence
              (append
               (trbr-depths depth (trbr-leaf))
               tail))
           (and
            (<= 0 (- (trbr-head sequence) depth))
            (<
             (- (trbr-head sequence) (+ depth 1))
             (- (trbr-head sequence) depth))
            (trbr-all-left-results-p sequence depth)
            (implies
             (trbr-no-prefix-tree-p
              (+ depth 1) sequence)
             (trbr-no-prefix-tree-p
              depth sequence)))))))))

(value-triple :itpeval-statement-checked)
:q
