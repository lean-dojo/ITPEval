;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_insertqtvc: the AVL insertion verification condition
;; for selector-guided sequence splitting and bounded height increase.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the arbitrary source carriers t, t1 alpha,
;; t2 alpha, selector, and part at a fixed arbitrary inhabited alpha.

(defstub avl-ins-t-p (x) t)
(defstub avl-ins-t1-p (x) t)
(defstub avl-ins-t2-p (x) t)
(defstub avl-ins-selector-p (x) t)
(defstub avl-ins-part-p (x) t)

(defstub avl-ins-zero () t)
(defstub avl-ins-op (left right) t)
(defstub avl-ins-measure (datum) t)
(defstub avl-ins-measure-closure (datum) t)
(defstub avl-ins-aggregate (sequence) t)
(defstub avl-ins-balancing () t)
(defstub avl-ins-repr (object) t)
(defstub avl-ins-m1 (object) t)
(defstub avl-ins-selected (selector split) t)
(defstub avl-ins-selection-possible (selector sequence) t)

(defun avl-ins-t1-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (avl-ins-t1-p (car xs))
     (avl-ins-t1-list-p (cdr xs)))))

;; Empty trees are NIL. Nodes are exact records
;; (:TREE-NODE left datum right height summary).

(defun avl-ins-tree-empty-p (tree)
  (equal tree nil))

(defun avl-ins-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun avl-ins-tree-left (tree)
  (cadr tree))

(defun avl-ins-tree-datum (tree)
  (caddr tree))

(defun avl-ins-tree-right (tree)
  (cadddr tree))

(defun avl-ins-tree-height (tree)
  (car (cddddr tree)))

(defun avl-ins-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avl-ins-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-ins-tree-empty-p tree)
      t
    (and
     (avl-ins-tree-node-shape-p tree)
     (avl-ins-tree-p (avl-ins-tree-left tree))
     (avl-ins-t1-p (avl-ins-tree-datum tree))
     (avl-ins-tree-p (avl-ins-tree-right tree))
     (natp (avl-ins-tree-height tree))
     (avl-ins-t-p (avl-ins-tree-summary tree)))))

;; The source model record m is represented exactly as
;; (:M sequence integer-height).

(defun avl-ins-m-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (avl-ins-t1-list-p (cadr model))
   (integerp (caddr model))))

(defun avl-ins-m-seq (model)
  (cadr model))

(defun avl-ins-m-hgt (model)
  (caddr model))

(defun avl-ins-node-model (left datum right)
  (append left (cons datum right)))

(defun avl-ins-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-ins-tree-empty-p tree)
      nil
    (if (avl-ins-tree-node-shape-p tree)
        (avl-ins-node-model
         (avl-ins-seq-model (avl-ins-tree-left tree))
         (avl-ins-tree-datum tree)
         (avl-ins-seq-model (avl-ins-tree-right tree)))
      nil)))

(defun avl-ins-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-ins-tree-empty-p tree)
      0
    (if (avl-ins-tree-node-shape-p tree)
        (let ((left-height
               (avl-ins-real-height
                (avl-ins-tree-left tree)))
              (right-height
               (avl-ins-real-height
                (avl-ins-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avl-ins-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-ins-tree-empty-p tree)
      t
    (if (avl-ins-tree-node-shape-p tree)
        (let* ((left (avl-ins-tree-left tree))
               (right (avl-ins-tree-right tree))
               (height (avl-ins-tree-height tree))
               (summary (avl-ins-tree-summary tree))
               (difference
                (- (avl-ins-real-height right)
                   (avl-ins-real-height left))))
          (and
           (equal height (avl-ins-real-height tree))
           (equal
            summary
            (avl-ins-aggregate
             (avl-ins-seq-model tree)))
           (<= (- (avl-ins-balancing)) difference)
           (<= difference (avl-ins-balancing))
           (avl-ins-balanced-p left)
           (avl-ins-balanced-p right)))
      nil)))

;; Empty views are NIL. Nodes are exact records
;; (:VIEW-NODE left datum right height summary).

(defun avl-ins-view-empty-p (view)
  (equal view nil))

(defun avl-ins-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun avl-ins-view-left (view)
  (cadr view))

(defun avl-ins-view-datum (view)
  (caddr view))

(defun avl-ins-view-right (view)
  (cadddr view))

(defun avl-ins-view-height (view)
  (car (cddddr view)))

(defun avl-ins-view-summary (view)
  (cadr (cddddr view)))

(defun avl-ins-view-p (view)
  (or
   (avl-ins-view-empty-p view)
   (and
    (avl-ins-view-node-shape-p view)
    (avl-ins-t2-p (avl-ins-view-left view))
    (avl-ins-t1-p (avl-ins-view-datum view))
    (avl-ins-t2-p (avl-ins-view-right view))
    (natp (avl-ins-view-height view))
    (avl-ins-t-p (avl-ins-view-summary view)))))

;; Options, splits, and selector-directed branches are exact tagged
;; representations of the source datatypes.

(defun avl-ins-none ()
  (list :none))

(defun avl-ins-some (datum)
  (list :some datum))

(defun avl-ins-option-p (option)
  (or
   (equal option (avl-ins-none))
   (and
    (true-listp option)
    (equal (len option) 2)
    (equal (car option) :some)
    (avl-ins-t1-p (cadr option)))))

(defun avl-ins-option-to-seq (option)
  (if (equal option (avl-ins-none))
      nil
    (list (cadr option))))

(defun avl-ins-split (left middle right)
  (list :split left middle right))

(defun avl-ins-split-p (split)
  (and
   (true-listp split)
   (equal (len split) 4)
   (equal (car split) :split)
   (avl-ins-t1-list-p (cadr split))
   (avl-ins-option-p (caddr split))
   (avl-ins-t1-list-p (cadddr split))))

(defun avl-ins-split-left (split)
  (cadr split))

(defun avl-ins-split-middle (split)
  (caddr split))

(defun avl-ins-split-right (split)
  (cadddr split))

(defun avl-ins-rebuild (split)
  (append
   (append
    (avl-ins-split-left split)
    (avl-ins-option-to-seq
     (avl-ins-split-middle split)))
   (avl-ins-split-right split)))

(defun avl-ins-left-extend (left datum split)
  (avl-ins-split
   (append
    left
    (cons datum
          (avl-ins-split-left split)))
   (avl-ins-split-middle split)
   (avl-ins-split-right split)))

(defun avl-ins-right-extend (split datum right)
  (avl-ins-split
   (avl-ins-split-left split)
   (avl-ins-split-middle split)
   (append
    (avl-ins-split-right split)
    (cons datum right))))

(defun avl-ins-here ()
  (list :here))

(defun avl-ins-left-branch (selector)
  (list :left selector))

(defun avl-ins-right-branch (selector)
  (list :right selector))

(defun avl-ins-part-base-p (branch)
  (or
   (equal branch (avl-ins-here))
   (and
    (true-listp branch)
    (equal (len branch) 2)
    (or
     (equal (car branch) :left)
     (equal (car branch) :right))
    (avl-ins-selector-p (cadr branch)))))

(defun avl-ins-left-branch-p (branch)
  (and
   (consp branch)
   (equal (car branch) :left)))

(defun avl-ins-right-branch-p (branch)
  (and
   (consp branch)
   (equal (car branch) :right)))

(defun avl-ins-branch-selector (branch)
  (cadr branch))

;; The source theory's carrier nonemptiness, typing, monoid and aggregation
;; laws, positive balance bound, representation invariant, injectivity, and
;; empty-selection law remain explicit assumptions of the statement.

(defun-sk avl-ins-carriers-inhabited-p ()
  (exists (datum object selector part)
    (and
     (avl-ins-t1-p datum)
     (avl-ins-t2-p object)
     (avl-ins-selector-p selector)
     (avl-ins-part-p part))))

(defun-sk avl-ins-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avl-ins-t-p left)
       (avl-ins-t-p right))
      (avl-ins-t-p
       (avl-ins-op left right)))
     (implies
      (avl-ins-t1-p datum)
      (and
       (avl-ins-t-p
        (avl-ins-measure datum))
       (avl-ins-t-p
        (avl-ins-measure-closure datum))))
     (implies
      (avl-ins-t1-list-p sequence)
      (avl-ins-t-p
       (avl-ins-aggregate sequence)))
     (implies
      (avl-ins-t2-p object)
      (and
       (avl-ins-tree-p
        (avl-ins-repr object))
       (avl-ins-m-p
        (avl-ins-m1 object)))))))

(defun-sk avl-ins-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avl-ins-t-p a)
      (avl-ins-t-p b)
      (avl-ins-t-p c))
     (equal
      (avl-ins-op a (avl-ins-op b c))
      (avl-ins-op (avl-ins-op a b) c)))))

(defun-sk avl-ins-neutral-p ()
  (forall (x)
    (implies
     (avl-ins-t-p x)
     (and
      (equal
       (avl-ins-op x (avl-ins-zero))
       x)
      (equal
       x
       (avl-ins-op (avl-ins-zero) x))))))

(defun-sk avl-ins-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avl-ins-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avl-ins-aggregate sequence)
      (avl-ins-measure-closure
       (car sequence))))))

(defun-sk avl-ins-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avl-ins-t1-list-p left)
      (avl-ins-t1-list-p right))
     (equal
      (avl-ins-aggregate
       (append left right))
      (avl-ins-op
       (avl-ins-aggregate left)
       (avl-ins-aggregate right))))))

(defun-sk avl-ins-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avl-ins-t1-p datum)
     (equal
      (avl-ins-measure-closure datum)
      (avl-ins-measure datum)))))

(defun-sk avl-ins-invariant-p ()
  (forall (object)
    (implies
     (avl-ins-t2-p object)
     (let ((tree (avl-ins-repr object))
           (model (avl-ins-m1 object)))
       (and
        (avl-ins-balanced-p tree)
        (equal
         (avl-ins-m-seq model)
         (avl-ins-seq-model tree))
        (equal
         (avl-ins-m-hgt model)
         (avl-ins-real-height tree)))))))

(defun-sk avl-ins-t2-injective-p ()
  (forall (left right)
    (implies
     (and
      (avl-ins-t2-p left)
      (avl-ins-t2-p right)
      (equal
       (avl-ins-repr left)
       (avl-ins-repr right))
      (equal
       (avl-ins-m1 left)
       (avl-ins-m1 right)))
     (equal left right))))

(defun-sk avl-ins-selection-empty-law-p ()
  (forall (selector)
    (implies
     (avl-ins-selector-p selector)
     (implies
      (avl-ins-selection-possible selector nil)
      (avl-ins-selected
       selector
       (avl-ins-split
        nil
        (avl-ins-none)
        nil))))))

(defun avl-ins-background-p ()
  (and
   (avl-ins-t-p (avl-ins-zero))
   (natp (avl-ins-balancing))
   (< 0 (avl-ins-balancing))
   (avl-ins-carriers-inhabited-p)
   (avl-ins-function-closures-p)
   (avl-ins-associative-p)
   (avl-ins-neutral-p)
   (equal
    (avl-ins-aggregate nil)
    (avl-ins-zero))
   (avl-ins-aggregate-singleton-law-p)
   (avl-ins-aggregate-concatenation-law-p)
   (avl-ins-measure-closure-law-p)
   (avl-ins-invariant-p)
   (avl-ins-t2-injective-p)
   (avl-ins-selection-empty-law-p)))

(defun avl-ins-sequence (object)
  (avl-ins-m-seq
   (avl-ins-m1 object)))

(defun avl-ins-height (object)
  (avl-ins-m-hgt
   (avl-ins-m1 object)))

(defun avl-ins-max (left right)
  (if (< left right)
      right
    left))

(defun avl-ins-within-balance-p (left-height right-height)
  (let ((difference (- left-height right-height)))
    (and
     (<= (- (avl-ins-balancing)) difference)
     (<= difference (avl-ins-balancing)))))

(defun avl-ins-height-increase-one-p (new-height old-height)
  (let ((difference (- new-height old-height)))
    (and
     (<= difference 1)
     (<= 0 difference))))

(defun avl-ins-near-node-height-exact-if-balanced-p
    (left right result)
  (let ((expected
         (+ 1
            (avl-ins-max
             (avl-ins-height left)
             (avl-ins-height right)))))
    (and
     (let ((height-error
            (- expected
               (avl-ins-height result))))
       (and
        (<= 0 height-error)
        (<= height-error 1)))
     (implies
      (avl-ins-within-balance-p
       (avl-ins-height left)
       (avl-ins-height right))
      (equal expected
             (avl-ins-height result))))))

;; The second theorem premise is preserved with its complete view case split.

(defun avl-ins-view-fact-p (view t3)
  (if (avl-ins-view-empty-p view)
      (and
       (equal (avl-ins-height t3) 0)
       (equal (avl-ins-sequence t3) nil))
    (let* ((left (avl-ins-view-left view))
           (datum (avl-ins-view-datum view))
           (right (avl-ins-view-right view))
           (height (avl-ins-view-height view))
           (summary (avl-ins-view-summary view)))
      (and
       (equal
        (avl-ins-sequence t3)
        (avl-ins-node-model
         (avl-ins-sequence left)
         datum
         (avl-ins-sequence right)))
       (equal
        summary
        (avl-ins-aggregate
         (avl-ins-sequence t3)))
       (avl-ins-within-balance-p
        (avl-ins-height left)
        (avl-ins-height right))
       (equal
        (avl-ins-height t3)
        height)
       (equal
        height
        (+ 1
           (avl-ins-max
            (avl-ins-height left)
            (avl-ins-height right))))))))

(defun-sk avl-ins-left-selection-continuation-p
    (selector subselector left-sequence datum right-sequence)
  (forall (split)
    (implies
     (avl-ins-split-p split)
     (implies
      (and
       (avl-ins-selected subselector split)
       (equal
        (avl-ins-rebuild split)
        left-sequence))
      (avl-ins-selected
       selector
       (avl-ins-right-extend
        split datum right-sequence))))))

(defun-sk avl-ins-right-selection-continuation-p
    (selector subselector left-sequence datum right-sequence)
  (forall (split)
    (implies
     (avl-ins-split-p split)
     (implies
      (and
       (avl-ins-selected subselector split)
       (equal
        (avl-ins-rebuild split)
        right-sequence))
      (avl-ins-selected
       selector
       (avl-ins-left-extend
        left-sequence datum split))))))

(defun avl-ins-part-premise-p
    (branch selector left-sequence datum right-sequence)
  (cond
   ((equal branch (avl-ins-here))
    (avl-ins-selected
     selector
     (avl-ins-split
      left-sequence
      (avl-ins-some datum)
      right-sequence)))
   ((avl-ins-left-branch-p branch)
    (let ((subselector
           (avl-ins-branch-selector branch)))
      (and
       (avl-ins-selection-possible
        subselector left-sequence)
       (avl-ins-left-selection-continuation-p
        selector subselector
        left-sequence datum right-sequence))))
   (t
    (let ((subselector
           (avl-ins-branch-selector branch)))
      (and
       (avl-ins-selection-possible
        subselector right-sequence)
       (avl-ins-right-selection-continuation-p
        selector subselector
        left-sequence datum right-sequence))))))

(defun avl-ins-result-conclusion-p
    (selector t3 result split inserted-datum)
  (and
   (equal
    (avl-ins-sequence result)
    (avl-ins-node-model
     (avl-ins-split-left split)
     inserted-datum
     (avl-ins-split-right split)))
   (and
    (avl-ins-selected selector split)
    (equal
     (avl-ins-rebuild split)
     (avl-ins-sequence t3)))
   (avl-ins-height-increase-one-p
    (avl-ins-height result)
    (avl-ins-height t3))))

(defun-sk avl-ins-empty-result-obligation-p
    (selector t3 inserted-datum)
  (forall (result)
    (implies
     (avl-ins-t2-p result)
     (implies
      (and
       (equal
        (avl-ins-sequence result)
        (list inserted-datum))
       (equal
        (avl-ins-height result)
        1))
      (avl-ins-result-conclusion-p
       selector t3 result
       (avl-ins-split
        nil
        (avl-ins-none)
        nil)
       inserted-datum)))))

;; Left recursive insertion branch. Every split, recursive tree, and rebuilt
;; result remains universally quantified at the same scope as in the source.

(defun-sk avl-ins-left-result-obligation-p
    (selector t3 tree-left node-datum tree-right
              split new-left inserted-datum)
  (forall (result)
    (implies
     (avl-ins-t2-p result)
     (implies
      (and
       (equal
        (avl-ins-sequence result)
        (avl-ins-node-model
         (avl-ins-sequence new-left)
         node-datum
         (avl-ins-sequence tree-right)))
       (avl-ins-near-node-height-exact-if-balanced-p
        new-left tree-right result))
      (avl-ins-result-conclusion-p
       selector t3 result
       (avl-ins-right-extend
        split node-datum
        (avl-ins-sequence tree-right))
       inserted-datum)))))

(defun-sk avl-ins-left-recursive-obligations-p
    (selector t3 tree-left node-datum tree-right
              subselector inserted-datum)
  (forall (split new-left)
    (implies
     (and
      (avl-ins-split-p split)
      (avl-ins-t2-p new-left))
     (implies
      (and
       (equal
        (avl-ins-sequence new-left)
        (avl-ins-node-model
         (avl-ins-split-left split)
         inserted-datum
         (avl-ins-split-right split)))
       (and
        (avl-ins-selected subselector split)
        (equal
         (avl-ins-rebuild split)
         (avl-ins-sequence tree-left)))
       (avl-ins-height-increase-one-p
        (avl-ins-height new-left)
        (avl-ins-height tree-left)))
      (and
       (let ((difference
              (- (avl-ins-height new-left)
                 (avl-ins-height tree-right))))
         (and
          (<=
           (- (- (avl-ins-balancing)) 1)
           difference)
          (<=
           difference
           (+ (avl-ins-balancing) 1))))
       (avl-ins-left-result-obligation-p
        selector t3 tree-left node-datum tree-right
        split new-left inserted-datum))))))

(defun avl-ins-left-conclusion-p
    (selector t3 tree-left node-datum tree-right
              subselector inserted-datum)
  (and
   (and
    (and
     (<= 0 (avl-ins-height t3))
     (<
      (avl-ins-height tree-left)
      (avl-ins-height t3)))
    (avl-ins-selection-possible
     subselector
     (avl-ins-sequence tree-left)))
   (avl-ins-left-recursive-obligations-p
    selector t3 tree-left node-datum tree-right
    subselector inserted-datum)))

;; Right recursive insertion branch, symmetric to the source's Left branch.

(defun-sk avl-ins-right-result-obligation-p
    (selector t3 tree-left node-datum tree-right
              split new-right inserted-datum)
  (forall (result)
    (implies
     (avl-ins-t2-p result)
     (implies
      (and
       (equal
        (avl-ins-sequence result)
        (avl-ins-node-model
         (avl-ins-sequence tree-left)
         node-datum
         (avl-ins-sequence new-right)))
       (avl-ins-near-node-height-exact-if-balanced-p
        tree-left new-right result))
      (avl-ins-result-conclusion-p
       selector t3 result
       (avl-ins-left-extend
        (avl-ins-sequence tree-left)
        node-datum split)
       inserted-datum)))))

(defun-sk avl-ins-right-recursive-obligations-p
    (selector t3 tree-left node-datum tree-right
              subselector inserted-datum)
  (forall (split new-right)
    (implies
     (and
      (avl-ins-split-p split)
      (avl-ins-t2-p new-right))
     (implies
      (and
       (equal
        (avl-ins-sequence new-right)
        (avl-ins-node-model
         (avl-ins-split-left split)
         inserted-datum
         (avl-ins-split-right split)))
       (and
        (avl-ins-selected subselector split)
        (equal
         (avl-ins-rebuild split)
         (avl-ins-sequence tree-right)))
       (avl-ins-height-increase-one-p
        (avl-ins-height new-right)
        (avl-ins-height tree-right)))
      (and
       (let ((difference
              (- (avl-ins-height tree-left)
                 (avl-ins-height new-right))))
         (and
          (<=
           (- (- (avl-ins-balancing)) 1)
           difference)
          (<=
           difference
           (+ (avl-ins-balancing) 1))))
       (avl-ins-right-result-obligation-p
        selector t3 tree-left node-datum tree-right
        split new-right inserted-datum))))))

(defun avl-ins-right-conclusion-p
    (selector t3 tree-left node-datum tree-right
              subselector inserted-datum)
  (and
   (and
    (and
     (<= 0 (avl-ins-height t3))
     (<
      (avl-ins-height tree-right)
      (avl-ins-height t3)))
    (avl-ins-selection-possible
     subselector
     (avl-ins-sequence tree-right)))
   (avl-ins-right-recursive-obligations-p
    selector t3 tree-left node-datum tree-right
    subselector inserted-datum)))

;; Root-selection insertion branch.

(defun-sk avl-ins-here-result-obligation-p
    (selector t3 tree-left node-datum tree-right inserted-datum)
  (forall (result)
    (implies
     (avl-ins-t2-p result)
     (implies
      (and
       (equal
        (avl-ins-sequence result)
        (avl-ins-node-model
         (avl-ins-sequence tree-left)
         inserted-datum
         (avl-ins-sequence tree-right)))
       (equal
        (avl-ins-height result)
        (+ 1
           (avl-ins-max
            (avl-ins-height tree-left)
            (avl-ins-height tree-right)))))
      (avl-ins-result-conclusion-p
       selector t3 result
       (avl-ins-split
        (avl-ins-sequence tree-left)
        (avl-ins-some node-datum)
        (avl-ins-sequence tree-right))
       inserted-datum)))))

(defun avl-ins-here-conclusion-p
    (selector t3 tree-left node-datum tree-right inserted-datum)
  (and
   (avl-ins-within-balance-p
    (avl-ins-height tree-left)
    (avl-ins-height tree-right))
   (avl-ins-here-result-obligation-p
    selector t3 tree-left node-datum tree-right inserted-datum)))

(defun avl-ins-part-conclusion-p
    (branch selector t3 tree-left node-datum tree-right inserted-datum)
  (cond
   ((avl-ins-left-branch-p branch)
    (avl-ins-left-conclusion-p
     selector t3 tree-left node-datum tree-right
     (avl-ins-branch-selector branch)
     inserted-datum))
   ((avl-ins-right-branch-p branch)
    (avl-ins-right-conclusion-p
     selector t3 tree-left node-datum tree-right
     (avl-ins-branch-selector branch)
     inserted-datum))
   (t
    (avl-ins-here-conclusion-p
     selector t3 tree-left node-datum tree-right inserted-datum))))

(defun-sk avl-ins-all-parts-obligation-p
    (selector t3 tree-left node-datum tree-right inserted-datum)
  (forall (branch)
    (implies
     (avl-ins-part-base-p branch)
     (implies
      (avl-ins-part-premise-p
       branch selector
       (avl-ins-sequence tree-left)
       node-datum
       (avl-ins-sequence tree-right))
      (avl-ins-part-conclusion-p
       branch selector t3 tree-left node-datum tree-right
       inserted-datum)))))

(defun avl-ins-node-conclusion-p
    (selector t3 tree-left node-datum tree-right inserted-datum)
  (let ((left-sequence
         (avl-ins-sequence tree-left))
        (right-sequence
         (avl-ins-sequence tree-right)))
    (and
     (and
      (avl-ins-selection-possible
       selector
       (avl-ins-node-model
        left-sequence node-datum right-sequence))
      (equal
       (avl-ins-aggregate
        (avl-ins-sequence tree-left))
       (avl-ins-aggregate left-sequence))
      (equal
       (avl-ins-aggregate
        (avl-ins-sequence tree-right))
       (avl-ins-aggregate right-sequence)))
     (avl-ins-all-parts-obligation-p
      selector t3 tree-left node-datum tree-right inserted-datum))))

(defun avl-ins-conclusion-p (selector t3 view inserted-datum)
  (if (avl-ins-view-empty-p view)
      (avl-ins-empty-result-obligation-p
       selector t3 inserted-datum)
    (avl-ins-node-conclusion-p
     selector
     t3
     (avl-ins-view-left view)
     (avl-ins-view-datum view)
     (avl-ins-view-right view)
     inserted-datum)))

(defun-sk ntp4vc-pearl-avl-avl-insertqtvc-statement ()
  (forall (selector t3 view inserted-datum)
    (implies
     (and
      (avl-ins-selector-p selector)
      (avl-ins-t2-p t3)
      (avl-ins-view-p view)
      (avl-ins-t1-p inserted-datum))
     (implies
      (and
       (avl-ins-background-p)
       (avl-ins-selection-possible
        selector
        (avl-ins-sequence t3))
       (avl-ins-view-fact-p view t3))
      (avl-ins-conclusion-p
       selector t3 view inserted-datum)))))

(value-triple :itpeval-statement-checked)
:q
