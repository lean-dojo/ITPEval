;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_extractqtvc: the AVL extraction verification condition
;; for selector-guided sequence splitting and bounded height change.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the arbitrary source carriers t, t1 alpha,
;; t2 alpha, selector, and part at a fixed arbitrary inhabited alpha.

(defstub avl-ext-t-p (x) t)
(defstub avl-ext-t1-p (x) t)
(defstub avl-ext-t2-p (x) t)
(defstub avl-ext-selector-p (x) t)
(defstub avl-ext-part-p (x) t)

(defstub avl-ext-zero () t)
(defstub avl-ext-op (left right) t)
(defstub avl-ext-measure (datum) t)
(defstub avl-ext-measure-closure (datum) t)
(defstub avl-ext-aggregate (sequence) t)
(defstub avl-ext-balancing () t)
(defstub avl-ext-repr (object) t)
(defstub avl-ext-m1 (object) t)
(defstub avl-ext-selected (selector split) t)
(defstub avl-ext-selection-possible (selector sequence) t)

(defun avl-ext-t1-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (avl-ext-t1-p (car xs))
     (avl-ext-t1-list-p (cdr xs)))))

;; Empty trees are NIL. Nodes are exact records
;; (:TREE-NODE left datum right height summary).

(defun avl-ext-tree-empty-p (tree)
  (equal tree nil))

(defun avl-ext-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun avl-ext-tree-left (tree)
  (cadr tree))

(defun avl-ext-tree-datum (tree)
  (caddr tree))

(defun avl-ext-tree-right (tree)
  (cadddr tree))

(defun avl-ext-tree-height (tree)
  (car (cddddr tree)))

(defun avl-ext-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avl-ext-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-ext-tree-empty-p tree)
      t
    (and
     (avl-ext-tree-node-shape-p tree)
     (avl-ext-tree-p (avl-ext-tree-left tree))
     (avl-ext-t1-p (avl-ext-tree-datum tree))
     (avl-ext-tree-p (avl-ext-tree-right tree))
     (natp (avl-ext-tree-height tree))
     (avl-ext-t-p (avl-ext-tree-summary tree)))))

;; The source model record m is represented exactly as
;; (:M sequence integer-height).

(defun avl-ext-m-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (avl-ext-t1-list-p (cadr model))
   (integerp (caddr model))))

(defun avl-ext-m-seq (model)
  (cadr model))

(defun avl-ext-m-hgt (model)
  (caddr model))

(defun avl-ext-node-model (left datum right)
  (append left (cons datum right)))

(defun avl-ext-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-ext-tree-empty-p tree)
      nil
    (if (avl-ext-tree-node-shape-p tree)
        (avl-ext-node-model
         (avl-ext-seq-model (avl-ext-tree-left tree))
         (avl-ext-tree-datum tree)
         (avl-ext-seq-model (avl-ext-tree-right tree)))
      nil)))

(defun avl-ext-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-ext-tree-empty-p tree)
      0
    (if (avl-ext-tree-node-shape-p tree)
        (let ((left-height
               (avl-ext-real-height
                (avl-ext-tree-left tree)))
              (right-height
               (avl-ext-real-height
                (avl-ext-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avl-ext-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-ext-tree-empty-p tree)
      t
    (if (avl-ext-tree-node-shape-p tree)
        (let* ((left (avl-ext-tree-left tree))
               (right (avl-ext-tree-right tree))
               (height (avl-ext-tree-height tree))
               (summary (avl-ext-tree-summary tree))
               (difference
                (- (avl-ext-real-height right)
                   (avl-ext-real-height left))))
          (and
           (equal height (avl-ext-real-height tree))
           (equal
            summary
            (avl-ext-aggregate
             (avl-ext-seq-model tree)))
           (<= (- (avl-ext-balancing)) difference)
           (<= difference (avl-ext-balancing))
           (avl-ext-balanced-p left)
           (avl-ext-balanced-p right)))
      nil)))

;; Empty views are NIL. Nodes are exact records
;; (:VIEW-NODE left datum right height summary).

(defun avl-ext-view-empty-p (view)
  (equal view nil))

(defun avl-ext-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun avl-ext-view-left (view)
  (cadr view))

(defun avl-ext-view-datum (view)
  (caddr view))

(defun avl-ext-view-right (view)
  (cadddr view))

(defun avl-ext-view-height (view)
  (car (cddddr view)))

(defun avl-ext-view-summary (view)
  (cadr (cddddr view)))

(defun avl-ext-view-p (view)
  (or
   (avl-ext-view-empty-p view)
   (and
    (avl-ext-view-node-shape-p view)
    (avl-ext-t2-p (avl-ext-view-left view))
    (avl-ext-t1-p (avl-ext-view-datum view))
    (avl-ext-t2-p (avl-ext-view-right view))
    (natp (avl-ext-view-height view))
    (avl-ext-t-p (avl-ext-view-summary view)))))

;; Options, splits, and selector-directed branches are exact tagged
;; representations of the source datatypes.

(defun avl-ext-none ()
  (list :none))

(defun avl-ext-some (datum)
  (list :some datum))

(defun avl-ext-option-p (option)
  (or
   (equal option (avl-ext-none))
   (and
    (true-listp option)
    (equal (len option) 2)
    (equal (car option) :some)
    (avl-ext-t1-p (cadr option)))))

(defun avl-ext-option-to-seq (option)
  (if (equal option (avl-ext-none))
      nil
    (list (cadr option))))

(defun avl-ext-split (left middle right)
  (list :split left middle right))

(defun avl-ext-split-p (split)
  (and
   (true-listp split)
   (equal (len split) 4)
   (equal (car split) :split)
   (avl-ext-t1-list-p (cadr split))
   (avl-ext-option-p (caddr split))
   (avl-ext-t1-list-p (cadddr split))))

(defun avl-ext-split-left (split)
  (cadr split))

(defun avl-ext-split-middle (split)
  (caddr split))

(defun avl-ext-split-right (split)
  (cadddr split))

(defun avl-ext-rebuild (split)
  (append
   (append
    (avl-ext-split-left split)
    (avl-ext-option-to-seq
     (avl-ext-split-middle split)))
   (avl-ext-split-right split)))

(defun avl-ext-left-extend (left datum split)
  (avl-ext-split
   (append
    left
    (cons datum
          (avl-ext-split-left split)))
   (avl-ext-split-middle split)
   (avl-ext-split-right split)))

(defun avl-ext-right-extend (split datum right)
  (avl-ext-split
   (avl-ext-split-left split)
   (avl-ext-split-middle split)
   (append
    (avl-ext-split-right split)
    (cons datum right))))

(defun avl-ext-here ()
  (list :here))

(defun avl-ext-left-branch (selector)
  (list :left selector))

(defun avl-ext-right-branch (selector)
  (list :right selector))

(defun avl-ext-part-base-p (branch)
  (or
   (equal branch (avl-ext-here))
   (and
    (true-listp branch)
    (equal (len branch) 2)
    (or
     (equal (car branch) :left)
     (equal (car branch) :right))
    (avl-ext-selector-p (cadr branch)))))

(defun avl-ext-left-branch-p (branch)
  (and
   (consp branch)
   (equal (car branch) :left)))

(defun avl-ext-right-branch-p (branch)
  (and
   (consp branch)
   (equal (car branch) :right)))

(defun avl-ext-branch-selector (branch)
  (cadr branch))

;; The source theory's carrier nonemptiness, typing, monoid and aggregation
;; laws, positive balance bound, representation invariant, injectivity, and
;; empty-selection law remain explicit assumptions of the statement.

(defun-sk avl-ext-carriers-inhabited-p ()
  (exists (datum object selector part)
    (and
     (avl-ext-t1-p datum)
     (avl-ext-t2-p object)
     (avl-ext-selector-p selector)
     (avl-ext-part-p part))))

(defun-sk avl-ext-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avl-ext-t-p left)
       (avl-ext-t-p right))
      (avl-ext-t-p
       (avl-ext-op left right)))
     (implies
      (avl-ext-t1-p datum)
      (and
       (avl-ext-t-p
        (avl-ext-measure datum))
       (avl-ext-t-p
        (avl-ext-measure-closure datum))))
     (implies
      (avl-ext-t1-list-p sequence)
      (avl-ext-t-p
       (avl-ext-aggregate sequence)))
     (implies
      (avl-ext-t2-p object)
      (and
       (avl-ext-tree-p
        (avl-ext-repr object))
       (avl-ext-m-p
        (avl-ext-m1 object)))))))

(defun-sk avl-ext-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avl-ext-t-p a)
      (avl-ext-t-p b)
      (avl-ext-t-p c))
     (equal
      (avl-ext-op a (avl-ext-op b c))
      (avl-ext-op (avl-ext-op a b) c)))))

(defun-sk avl-ext-neutral-p ()
  (forall (x)
    (implies
     (avl-ext-t-p x)
     (and
      (equal
       (avl-ext-op x (avl-ext-zero))
       x)
      (equal
       x
       (avl-ext-op (avl-ext-zero) x))))))

(defun-sk avl-ext-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avl-ext-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avl-ext-aggregate sequence)
      (avl-ext-measure-closure
       (car sequence))))))

(defun-sk avl-ext-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avl-ext-t1-list-p left)
      (avl-ext-t1-list-p right))
     (equal
      (avl-ext-aggregate
       (append left right))
      (avl-ext-op
       (avl-ext-aggregate left)
       (avl-ext-aggregate right))))))

(defun-sk avl-ext-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avl-ext-t1-p datum)
     (equal
      (avl-ext-measure-closure datum)
      (avl-ext-measure datum)))))

(defun-sk avl-ext-invariant-p ()
  (forall (object)
    (implies
     (avl-ext-t2-p object)
     (let ((tree (avl-ext-repr object))
           (model (avl-ext-m1 object)))
       (and
        (avl-ext-balanced-p tree)
        (equal
         (avl-ext-m-seq model)
         (avl-ext-seq-model tree))
        (equal
         (avl-ext-m-hgt model)
         (avl-ext-real-height tree)))))))

(defun-sk avl-ext-t2-injective-p ()
  (forall (left right)
    (implies
     (and
      (avl-ext-t2-p left)
      (avl-ext-t2-p right)
      (equal
       (avl-ext-repr left)
       (avl-ext-repr right))
      (equal
       (avl-ext-m1 left)
       (avl-ext-m1 right)))
     (equal left right))))

(defun-sk avl-ext-selection-empty-law-p ()
  (forall (selector)
    (implies
     (avl-ext-selector-p selector)
     (implies
      (avl-ext-selection-possible selector nil)
      (avl-ext-selected
       selector
       (avl-ext-split
        nil
        (avl-ext-none)
        nil))))))

(defun avl-ext-background-p ()
  (and
   (avl-ext-t-p (avl-ext-zero))
   (natp (avl-ext-balancing))
   (< 0 (avl-ext-balancing))
   (avl-ext-carriers-inhabited-p)
   (avl-ext-function-closures-p)
   (avl-ext-associative-p)
   (avl-ext-neutral-p)
   (equal
    (avl-ext-aggregate nil)
    (avl-ext-zero))
   (avl-ext-aggregate-singleton-law-p)
   (avl-ext-aggregate-concatenation-law-p)
   (avl-ext-measure-closure-law-p)
   (avl-ext-invariant-p)
   (avl-ext-t2-injective-p)
   (avl-ext-selection-empty-law-p)))

(defun avl-ext-sequence (object)
  (avl-ext-m-seq
   (avl-ext-m1 object)))

(defun avl-ext-height (object)
  (avl-ext-m-hgt
   (avl-ext-m1 object)))

(defun avl-ext-max (left right)
  (if (< left right)
      right
    left))

(defun avl-ext-within-balance-p (left-height right-height)
  (let ((difference (- left-height right-height)))
    (and
     (<= (- (avl-ext-balancing)) difference)
     (<= difference (avl-ext-balancing)))))

(defun avl-ext-height-drop-one-p (old-height new-height)
  (let ((difference (- old-height new-height)))
    (and
     (<= difference 1)
     (<= 0 difference))))

(defun avl-ext-near-node-height-p (left right result)
  (let ((expected
         (+ 1
            (avl-ext-max
             (avl-ext-height left)
             (avl-ext-height right)))))
    (avl-ext-height-drop-one-p
     expected
     (avl-ext-height result))))

(defun avl-ext-near-node-height-exact-if-balanced-p
    (left right result)
  (let ((expected
         (+ 1
            (avl-ext-max
             (avl-ext-height left)
             (avl-ext-height right)))))
    (and
     (avl-ext-height-drop-one-p
      expected
      (avl-ext-height result))
     (implies
      (avl-ext-within-balance-p
       (avl-ext-height left)
       (avl-ext-height right))
      (equal expected
             (avl-ext-height result))))))

;; The second theorem premise is preserved with its complete view case split.

(defun avl-ext-view-fact-p (view t3)
  (if (avl-ext-view-empty-p view)
      (and
       (equal (avl-ext-height t3) 0)
       (equal (avl-ext-sequence t3) nil))
    (let* ((left (avl-ext-view-left view))
           (datum (avl-ext-view-datum view))
           (right (avl-ext-view-right view))
           (height (avl-ext-view-height view))
           (summary (avl-ext-view-summary view)))
      (and
       (equal
        (avl-ext-sequence t3)
        (avl-ext-node-model
         (avl-ext-sequence left)
         datum
         (avl-ext-sequence right)))
       (equal
        summary
        (avl-ext-aggregate
         (avl-ext-sequence t3)))
       (avl-ext-within-balance-p
        (avl-ext-height left)
        (avl-ext-height right))
       (equal
        (avl-ext-height t3)
        height)
       (equal
        height
        (+ 1
           (avl-ext-max
            (avl-ext-height left)
            (avl-ext-height right))))))))

(defun avl-ext-empty-conclusion-p (selector t3)
  (let ((empty-split
         (avl-ext-split
          nil
          (avl-ext-none)
          nil)))
    (and
     (and
      (avl-ext-selected selector empty-split)
      (equal
       (avl-ext-rebuild empty-split)
       (avl-ext-sequence t3)))
     (equal
      (avl-ext-sequence t3)
      (append
       (avl-ext-split-left empty-split)
       (avl-ext-split-right empty-split)))
     (avl-ext-height-drop-one-p
      (avl-ext-height t3)
      (avl-ext-height t3))
     (equal
      (avl-ext-split-middle empty-split)
      (avl-ext-none)))))

;; These two predicates preserve the universal split continuations in the
;; Left and Right premises of the selector part_base case.

(defun-sk avl-ext-left-selection-continuation-p
    (selector subselector left-sequence datum right-sequence)
  (forall (split)
    (implies
     (avl-ext-split-p split)
     (implies
      (and
       (avl-ext-selected subselector split)
       (equal
        (avl-ext-rebuild split)
        left-sequence))
      (avl-ext-selected
       selector
       (avl-ext-right-extend
        split datum right-sequence))))))

(defun-sk avl-ext-right-selection-continuation-p
    (selector subselector left-sequence datum right-sequence)
  (forall (split)
    (implies
     (avl-ext-split-p split)
     (implies
      (and
       (avl-ext-selected subselector split)
       (equal
        (avl-ext-rebuild split)
        right-sequence))
      (avl-ext-selected
       selector
       (avl-ext-left-extend
        left-sequence datum split))))))

(defun avl-ext-part-premise-p
    (branch selector left-sequence datum right-sequence)
  (cond
   ((equal branch (avl-ext-here))
    (avl-ext-selected
     selector
     (avl-ext-split
      left-sequence
      (avl-ext-some datum)
      right-sequence)))
   ((avl-ext-left-branch-p branch)
    (let ((subselector
           (avl-ext-branch-selector branch)))
      (and
       (avl-ext-selection-possible
        subselector left-sequence)
       (avl-ext-left-selection-continuation-p
        selector subselector
        left-sequence datum right-sequence))))
   (t
    (let ((subselector
           (avl-ext-branch-selector branch)))
      (and
       (avl-ext-selection-possible
        subselector right-sequence)
       (avl-ext-right-selection-continuation-p
        selector subselector
        left-sequence datum right-sequence))))))

(defun avl-ext-result-conclusion-p
    (selector t3 result split option)
  (and
   (and
    (avl-ext-selected selector split)
    (equal
     (avl-ext-rebuild split)
     (avl-ext-sequence t3)))
   (equal
    (avl-ext-sequence result)
    (append
     (avl-ext-split-left split)
     (avl-ext-split-right split)))
   (avl-ext-height-drop-one-p
    (avl-ext-height t3)
    (avl-ext-height result))
   (equal
    (avl-ext-split-middle split)
    option)))

;; Left recursive branch: all split, option, recursive-tree, and rebuilt-tree
;; variables retain their source universal quantifier scopes.

(defun-sk avl-ext-left-result-obligation-p
    (selector t3 tree-left datum tree-right
              subselector split option new-left)
  (forall (result)
    (implies
     (avl-ext-t2-p result)
     (implies
      (and
       (equal
        (avl-ext-sequence result)
        (avl-ext-node-model
         (avl-ext-sequence new-left)
         datum
         (avl-ext-sequence tree-right)))
       (avl-ext-near-node-height-exact-if-balanced-p
        new-left tree-right result))
      (avl-ext-result-conclusion-p
       selector
       t3
       result
       (avl-ext-right-extend
        split datum
        (avl-ext-sequence tree-right))
       option)))))

(defun-sk avl-ext-left-recursive-obligations-p
    (selector t3 tree-left datum tree-right subselector)
  (forall (split option new-left)
    (implies
     (and
      (avl-ext-split-p split)
      (avl-ext-option-p option)
      (avl-ext-t2-p new-left))
     (implies
      (and
       (and
        (avl-ext-selected subselector split)
        (equal
         (avl-ext-rebuild split)
         (avl-ext-sequence tree-left)))
       (equal
        (avl-ext-sequence new-left)
        (append
         (avl-ext-split-left split)
         (avl-ext-split-right split)))
       (avl-ext-height-drop-one-p
        (avl-ext-height tree-left)
        (avl-ext-height new-left))
       (equal
        (avl-ext-split-middle split)
        option))
      (and
       (let ((difference
              (- (avl-ext-height new-left)
                 (avl-ext-height tree-right))))
         (and
          (<=
           (- (- (avl-ext-balancing)) 1)
           difference)
          (<=
           difference
           (+ (avl-ext-balancing) 1))))
       (avl-ext-left-result-obligation-p
        selector t3 tree-left datum tree-right
        subselector split option new-left))))))

(defun avl-ext-left-conclusion-p
    (selector t3 tree-left datum tree-right subselector)
  (and
   (and
    (and
     (<= 0 (avl-ext-height t3))
     (<
      (avl-ext-height tree-left)
      (avl-ext-height t3)))
    (avl-ext-selection-possible
     subselector
     (avl-ext-sequence tree-left)))
   (avl-ext-left-recursive-obligations-p
    selector t3 tree-left datum tree-right subselector)))

;; Right recursive branch, symmetric to the source's Left branch.

(defun-sk avl-ext-right-result-obligation-p
    (selector t3 tree-left datum tree-right
              subselector split option new-right)
  (forall (result)
    (implies
     (avl-ext-t2-p result)
     (implies
      (and
       (equal
        (avl-ext-sequence result)
        (avl-ext-node-model
         (avl-ext-sequence tree-left)
         datum
         (avl-ext-sequence new-right)))
       (avl-ext-near-node-height-exact-if-balanced-p
        tree-left new-right result))
      (avl-ext-result-conclusion-p
       selector
       t3
       result
       (avl-ext-left-extend
        (avl-ext-sequence tree-left)
        datum split)
       option)))))

(defun-sk avl-ext-right-recursive-obligations-p
    (selector t3 tree-left datum tree-right subselector)
  (forall (split option new-right)
    (implies
     (and
      (avl-ext-split-p split)
      (avl-ext-option-p option)
      (avl-ext-t2-p new-right))
     (implies
      (and
       (and
        (avl-ext-selected subselector split)
        (equal
         (avl-ext-rebuild split)
         (avl-ext-sequence tree-right)))
       (equal
        (avl-ext-sequence new-right)
        (append
         (avl-ext-split-left split)
         (avl-ext-split-right split)))
       (avl-ext-height-drop-one-p
        (avl-ext-height tree-right)
        (avl-ext-height new-right))
       (equal
        (avl-ext-split-middle split)
        option))
      (and
       (let ((difference
              (- (avl-ext-height tree-left)
                 (avl-ext-height new-right))))
         (and
          (<=
           (- (- (avl-ext-balancing)) 1)
           difference)
          (<=
           difference
           (+ (avl-ext-balancing) 1))))
       (avl-ext-right-result-obligation-p
        selector t3 tree-left datum tree-right
        subselector split option new-right))))))

(defun avl-ext-right-conclusion-p
    (selector t3 tree-left datum tree-right subselector)
  (and
   (and
    (and
     (<= 0 (avl-ext-height t3))
     (<
      (avl-ext-height tree-right)
      (avl-ext-height t3)))
    (avl-ext-selection-possible
     subselector
     (avl-ext-sequence tree-right)))
   (avl-ext-right-recursive-obligations-p
    selector t3 tree-left datum tree-right subselector)))

;; Root-selection branch.

(defun-sk avl-ext-here-result-obligation-p
    (selector t3 tree-left datum tree-right)
  (forall (result)
    (implies
     (avl-ext-t2-p result)
     (implies
      (and
       (equal
        (avl-ext-sequence result)
        (append
         (avl-ext-sequence tree-left)
         (avl-ext-sequence tree-right)))
       (avl-ext-near-node-height-p
        tree-left tree-right result))
      (avl-ext-result-conclusion-p
       selector
       t3
       result
       (avl-ext-split
        (avl-ext-sequence tree-left)
        (avl-ext-some datum)
        (avl-ext-sequence tree-right))
       (avl-ext-some datum))))))

(defun avl-ext-here-conclusion-p
    (selector t3 tree-left datum tree-right)
  (and
   (avl-ext-within-balance-p
    (avl-ext-height tree-left)
    (avl-ext-height tree-right))
   (avl-ext-here-result-obligation-p
    selector t3 tree-left datum tree-right)))

(defun avl-ext-part-conclusion-p
    (branch selector t3 tree-left datum tree-right)
  (cond
   ((avl-ext-left-branch-p branch)
    (avl-ext-left-conclusion-p
     selector t3 tree-left datum tree-right
     (avl-ext-branch-selector branch)))
   ((avl-ext-right-branch-p branch)
    (avl-ext-right-conclusion-p
     selector t3 tree-left datum tree-right
     (avl-ext-branch-selector branch)))
   (t
    (avl-ext-here-conclusion-p
     selector t3 tree-left datum tree-right))))

(defun-sk avl-ext-all-parts-obligation-p
    (selector t3 tree-left datum tree-right)
  (forall (branch)
    (implies
     (avl-ext-part-base-p branch)
     (implies
      (avl-ext-part-premise-p
       branch selector
       (avl-ext-sequence tree-left)
       datum
       (avl-ext-sequence tree-right))
      (avl-ext-part-conclusion-p
       branch selector t3
       tree-left datum tree-right)))))

(defun avl-ext-node-conclusion-p
    (selector t3 tree-left datum tree-right)
  (let ((left-sequence
         (avl-ext-sequence tree-left))
        (right-sequence
         (avl-ext-sequence tree-right)))
    (and
     (and
      (avl-ext-selection-possible
       selector
       (avl-ext-node-model
        left-sequence datum right-sequence))
      (equal
       (avl-ext-aggregate
        (avl-ext-sequence tree-left))
       (avl-ext-aggregate left-sequence))
      (equal
       (avl-ext-aggregate
        (avl-ext-sequence tree-right))
       (avl-ext-aggregate right-sequence)))
     (avl-ext-all-parts-obligation-p
      selector t3 tree-left datum tree-right))))

(defun avl-ext-conclusion-p (selector t3 view)
  (if (avl-ext-view-empty-p view)
      (avl-ext-empty-conclusion-p selector t3)
    (avl-ext-node-conclusion-p
     selector
     t3
     (avl-ext-view-left view)
     (avl-ext-view-datum view)
     (avl-ext-view-right view))))

(defun-sk ntp4vc-pearl-avl-avl-extractqtvc-statement ()
  (forall (selector t3 view)
    (implies
     (and
      (avl-ext-selector-p selector)
      (avl-ext-t2-p t3)
      (avl-ext-view-p view))
     (implies
      (and
       (avl-ext-background-p)
       (avl-ext-selection-possible
        selector
        (avl-ext-sequence t3))
       (avl-ext-view-fact-p view t3))
      (avl-ext-conclusion-p
       selector t3 view)))))

(value-triple :itpeval-statement-checked)
:q
