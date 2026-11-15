;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_removeqtvc: the AVL removal verification condition
;; for selector-guided sequence splitting and bounded height change.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the arbitrary source carriers t, t1 alpha,
;; t2 alpha, selector, and part at a fixed arbitrary inhabited alpha.

(defstub avl-rem-t-p (x) t)
(defstub avl-rem-t1-p (x) t)
(defstub avl-rem-t2-p (x) t)
(defstub avl-rem-selector-p (x) t)
(defstub avl-rem-part-p (x) t)

(defstub avl-rem-zero () t)
(defstub avl-rem-op (left right) t)
(defstub avl-rem-measure (datum) t)
(defstub avl-rem-measure-closure (datum) t)
(defstub avl-rem-aggregate (sequence) t)
(defstub avl-rem-balancing () t)
(defstub avl-rem-repr (object) t)
(defstub avl-rem-m1 (object) t)
(defstub avl-rem-selected (selector split) t)
(defstub avl-rem-selection-possible (selector sequence) t)

(defun avl-rem-t1-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (avl-rem-t1-p (car xs))
     (avl-rem-t1-list-p (cdr xs)))))

;; Empty trees are NIL. Nodes are exact records
;; (:TREE-NODE left datum right height summary).

(defun avl-rem-tree-empty-p (tree)
  (equal tree nil))

(defun avl-rem-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun avl-rem-tree-left (tree)
  (cadr tree))

(defun avl-rem-tree-datum (tree)
  (caddr tree))

(defun avl-rem-tree-right (tree)
  (cadddr tree))

(defun avl-rem-tree-height (tree)
  (car (cddddr tree)))

(defun avl-rem-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avl-rem-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-rem-tree-empty-p tree)
      t
    (and
     (avl-rem-tree-node-shape-p tree)
     (avl-rem-tree-p (avl-rem-tree-left tree))
     (avl-rem-t1-p (avl-rem-tree-datum tree))
     (avl-rem-tree-p (avl-rem-tree-right tree))
     (natp (avl-rem-tree-height tree))
     (avl-rem-t-p (avl-rem-tree-summary tree)))))

;; The source model record m is represented exactly as
;; (:M sequence integer-height).

(defun avl-rem-m-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (avl-rem-t1-list-p (cadr model))
   (integerp (caddr model))))

(defun avl-rem-m-seq (model)
  (cadr model))

(defun avl-rem-m-hgt (model)
  (caddr model))

(defun avl-rem-node-model (left datum right)
  (append left (cons datum right)))

(defun avl-rem-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-rem-tree-empty-p tree)
      nil
    (if (avl-rem-tree-node-shape-p tree)
        (avl-rem-node-model
         (avl-rem-seq-model (avl-rem-tree-left tree))
         (avl-rem-tree-datum tree)
         (avl-rem-seq-model (avl-rem-tree-right tree)))
      nil)))

(defun avl-rem-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-rem-tree-empty-p tree)
      0
    (if (avl-rem-tree-node-shape-p tree)
        (let ((left-height
               (avl-rem-real-height
                (avl-rem-tree-left tree)))
              (right-height
               (avl-rem-real-height
                (avl-rem-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avl-rem-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-rem-tree-empty-p tree)
      t
    (if (avl-rem-tree-node-shape-p tree)
        (let* ((left (avl-rem-tree-left tree))
               (right (avl-rem-tree-right tree))
               (height (avl-rem-tree-height tree))
               (summary (avl-rem-tree-summary tree))
               (difference
                (- (avl-rem-real-height right)
                   (avl-rem-real-height left))))
          (and
           (equal height (avl-rem-real-height tree))
           (equal
            summary
            (avl-rem-aggregate
             (avl-rem-seq-model tree)))
           (<= (- (avl-rem-balancing)) difference)
           (<= difference (avl-rem-balancing))
           (avl-rem-balanced-p left)
           (avl-rem-balanced-p right)))
      nil)))

;; Empty views are NIL. Nodes are exact records
;; (:VIEW-NODE left datum right height summary).

(defun avl-rem-view-empty-p (view)
  (equal view nil))

(defun avl-rem-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun avl-rem-view-left (view)
  (cadr view))

(defun avl-rem-view-datum (view)
  (caddr view))

(defun avl-rem-view-right (view)
  (cadddr view))

(defun avl-rem-view-height (view)
  (car (cddddr view)))

(defun avl-rem-view-summary (view)
  (cadr (cddddr view)))

(defun avl-rem-view-p (view)
  (or
   (avl-rem-view-empty-p view)
   (and
    (avl-rem-view-node-shape-p view)
    (avl-rem-t2-p (avl-rem-view-left view))
    (avl-rem-t1-p (avl-rem-view-datum view))
    (avl-rem-t2-p (avl-rem-view-right view))
    (natp (avl-rem-view-height view))
    (avl-rem-t-p (avl-rem-view-summary view)))))

;; Options, splits, and selector-directed branches are exact tagged
;; representations of the source datatypes.

(defun avl-rem-none ()
  (list :none))

(defun avl-rem-some (datum)
  (list :some datum))

(defun avl-rem-option-p (option)
  (or
   (equal option (avl-rem-none))
   (and
    (true-listp option)
    (equal (len option) 2)
    (equal (car option) :some)
    (avl-rem-t1-p (cadr option)))))

(defun avl-rem-option-to-seq (option)
  (if (equal option (avl-rem-none))
      nil
    (list (cadr option))))

(defun avl-rem-split (left middle right)
  (list :split left middle right))

(defun avl-rem-split-p (split)
  (and
   (true-listp split)
   (equal (len split) 4)
   (equal (car split) :split)
   (avl-rem-t1-list-p (cadr split))
   (avl-rem-option-p (caddr split))
   (avl-rem-t1-list-p (cadddr split))))

(defun avl-rem-split-left (split)
  (cadr split))

(defun avl-rem-split-middle (split)
  (caddr split))

(defun avl-rem-split-right (split)
  (cadddr split))

(defun avl-rem-rebuild (split)
  (append
   (append
    (avl-rem-split-left split)
    (avl-rem-option-to-seq
     (avl-rem-split-middle split)))
   (avl-rem-split-right split)))

(defun avl-rem-left-extend (left datum split)
  (avl-rem-split
   (append
    left
    (cons datum
          (avl-rem-split-left split)))
   (avl-rem-split-middle split)
   (avl-rem-split-right split)))

(defun avl-rem-right-extend (split datum right)
  (avl-rem-split
   (avl-rem-split-left split)
   (avl-rem-split-middle split)
   (append
    (avl-rem-split-right split)
    (cons datum right))))

(defun avl-rem-here ()
  (list :here))

(defun avl-rem-left-branch (selector)
  (list :left selector))

(defun avl-rem-right-branch (selector)
  (list :right selector))

(defun avl-rem-part-base-p (branch)
  (or
   (equal branch (avl-rem-here))
   (and
    (true-listp branch)
    (equal (len branch) 2)
    (or
     (equal (car branch) :left)
     (equal (car branch) :right))
    (avl-rem-selector-p (cadr branch)))))

(defun avl-rem-left-branch-p (branch)
  (and
   (consp branch)
   (equal (car branch) :left)))

(defun avl-rem-right-branch-p (branch)
  (and
   (consp branch)
   (equal (car branch) :right)))

(defun avl-rem-branch-selector (branch)
  (cadr branch))

;; The source theory's carrier nonemptiness, typing, monoid and aggregation
;; laws, positive balance bound, representation invariant, injectivity, and
;; empty-selection law remain explicit assumptions of the statement.

(defun-sk avl-rem-carriers-inhabited-p ()
  (exists (datum object selector part)
    (and
     (avl-rem-t1-p datum)
     (avl-rem-t2-p object)
     (avl-rem-selector-p selector)
     (avl-rem-part-p part))))

(defun-sk avl-rem-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avl-rem-t-p left)
       (avl-rem-t-p right))
      (avl-rem-t-p
       (avl-rem-op left right)))
     (implies
      (avl-rem-t1-p datum)
      (and
       (avl-rem-t-p
        (avl-rem-measure datum))
       (avl-rem-t-p
        (avl-rem-measure-closure datum))))
     (implies
      (avl-rem-t1-list-p sequence)
      (avl-rem-t-p
       (avl-rem-aggregate sequence)))
     (implies
      (avl-rem-t2-p object)
      (and
       (avl-rem-tree-p
        (avl-rem-repr object))
       (avl-rem-m-p
        (avl-rem-m1 object)))))))

(defun-sk avl-rem-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avl-rem-t-p a)
      (avl-rem-t-p b)
      (avl-rem-t-p c))
     (equal
      (avl-rem-op a (avl-rem-op b c))
      (avl-rem-op (avl-rem-op a b) c)))))

(defun-sk avl-rem-neutral-p ()
  (forall (x)
    (implies
     (avl-rem-t-p x)
     (and
      (equal
       (avl-rem-op x (avl-rem-zero))
       x)
      (equal
       x
       (avl-rem-op (avl-rem-zero) x))))))

(defun-sk avl-rem-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avl-rem-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avl-rem-aggregate sequence)
      (avl-rem-measure-closure
       (car sequence))))))

(defun-sk avl-rem-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avl-rem-t1-list-p left)
      (avl-rem-t1-list-p right))
     (equal
      (avl-rem-aggregate
       (append left right))
      (avl-rem-op
       (avl-rem-aggregate left)
       (avl-rem-aggregate right))))))

(defun-sk avl-rem-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avl-rem-t1-p datum)
     (equal
      (avl-rem-measure-closure datum)
      (avl-rem-measure datum)))))

(defun-sk avl-rem-invariant-p ()
  (forall (object)
    (implies
     (avl-rem-t2-p object)
     (let ((tree (avl-rem-repr object))
           (model (avl-rem-m1 object)))
       (and
        (avl-rem-balanced-p tree)
        (equal
         (avl-rem-m-seq model)
         (avl-rem-seq-model tree))
        (equal
         (avl-rem-m-hgt model)
         (avl-rem-real-height tree)))))))

(defun-sk avl-rem-t2-injective-p ()
  (forall (left right)
    (implies
     (and
      (avl-rem-t2-p left)
      (avl-rem-t2-p right)
      (equal
       (avl-rem-repr left)
       (avl-rem-repr right))
      (equal
       (avl-rem-m1 left)
       (avl-rem-m1 right)))
     (equal left right))))

(defun-sk avl-rem-selection-empty-law-p ()
  (forall (selector)
    (implies
     (avl-rem-selector-p selector)
     (implies
      (avl-rem-selection-possible selector nil)
      (avl-rem-selected
       selector
       (avl-rem-split
        nil
        (avl-rem-none)
        nil))))))

(defun avl-rem-background-p ()
  (and
   (avl-rem-t-p (avl-rem-zero))
   (natp (avl-rem-balancing))
   (< 0 (avl-rem-balancing))
   (avl-rem-carriers-inhabited-p)
   (avl-rem-function-closures-p)
   (avl-rem-associative-p)
   (avl-rem-neutral-p)
   (equal
    (avl-rem-aggregate nil)
    (avl-rem-zero))
   (avl-rem-aggregate-singleton-law-p)
   (avl-rem-aggregate-concatenation-law-p)
   (avl-rem-measure-closure-law-p)
   (avl-rem-invariant-p)
   (avl-rem-t2-injective-p)
   (avl-rem-selection-empty-law-p)))

(defun avl-rem-sequence (object)
  (avl-rem-m-seq
   (avl-rem-m1 object)))

(defun avl-rem-height (object)
  (avl-rem-m-hgt
   (avl-rem-m1 object)))

(defun avl-rem-max (left right)
  (if (< left right)
      right
    left))

(defun avl-rem-within-balance-p (left-height right-height)
  (let ((difference (- left-height right-height)))
    (and
     (<= (- (avl-rem-balancing)) difference)
     (<= difference (avl-rem-balancing)))))

(defun avl-rem-height-drop-one-p (old-height new-height)
  (let ((difference (- old-height new-height)))
    (and
     (<= difference 1)
     (<= 0 difference))))

(defun avl-rem-near-node-height-p (left right result)
  (let ((expected
         (+ 1
            (avl-rem-max
             (avl-rem-height left)
             (avl-rem-height right)))))
    (avl-rem-height-drop-one-p
     expected
     (avl-rem-height result))))

(defun avl-rem-near-node-height-exact-if-balanced-p
    (left right result)
  (let ((expected
         (+ 1
            (avl-rem-max
             (avl-rem-height left)
             (avl-rem-height right)))))
    (and
     (avl-rem-height-drop-one-p
      expected
      (avl-rem-height result))
     (implies
      (avl-rem-within-balance-p
       (avl-rem-height left)
       (avl-rem-height right))
      (equal expected
             (avl-rem-height result))))))

;; The second theorem premise is preserved with its complete view case split.

(defun avl-rem-view-fact-p (view t3)
  (if (avl-rem-view-empty-p view)
      (and
       (equal (avl-rem-height t3) 0)
       (equal (avl-rem-sequence t3) nil))
    (let* ((left (avl-rem-view-left view))
           (datum (avl-rem-view-datum view))
           (right (avl-rem-view-right view))
           (height (avl-rem-view-height view))
           (summary (avl-rem-view-summary view)))
      (and
       (equal
        (avl-rem-sequence t3)
        (avl-rem-node-model
         (avl-rem-sequence left)
         datum
         (avl-rem-sequence right)))
       (equal
        summary
        (avl-rem-aggregate
         (avl-rem-sequence t3)))
       (avl-rem-within-balance-p
        (avl-rem-height left)
        (avl-rem-height right))
       (equal
        (avl-rem-height t3)
        height)
       (equal
        height
        (+ 1
           (avl-rem-max
            (avl-rem-height left)
            (avl-rem-height right))))))))

(defun avl-rem-empty-conclusion-p (selector t3)
  (let ((empty-split
         (avl-rem-split
          nil
          (avl-rem-none)
          nil)))
    (and
     (equal
      (avl-rem-sequence t3)
      (append
       (avl-rem-split-left empty-split)
       (avl-rem-split-right empty-split)))
     (and
      (avl-rem-selected selector empty-split)
      (equal
       (avl-rem-rebuild empty-split)
       (avl-rem-sequence t3)))
     (avl-rem-height-drop-one-p
      (avl-rem-height t3)
      (avl-rem-height t3)))))

;; These two predicates preserve the universal split continuations in the
;; Left and Right premises of the selector part_base case.

(defun-sk avl-rem-left-selection-continuation-p
    (selector subselector left-sequence datum right-sequence)
  (forall (split)
    (implies
     (avl-rem-split-p split)
     (implies
      (and
       (avl-rem-selected subselector split)
       (equal
        (avl-rem-rebuild split)
        left-sequence))
      (avl-rem-selected
       selector
       (avl-rem-right-extend
        split datum right-sequence))))))

(defun-sk avl-rem-right-selection-continuation-p
    (selector subselector left-sequence datum right-sequence)
  (forall (split)
    (implies
     (avl-rem-split-p split)
     (implies
      (and
       (avl-rem-selected subselector split)
       (equal
        (avl-rem-rebuild split)
        right-sequence))
      (avl-rem-selected
       selector
       (avl-rem-left-extend
        left-sequence datum split))))))

(defun avl-rem-part-premise-p
    (branch selector left-sequence datum right-sequence)
  (cond
   ((equal branch (avl-rem-here))
    (avl-rem-selected
     selector
     (avl-rem-split
      left-sequence
      (avl-rem-some datum)
      right-sequence)))
   ((avl-rem-left-branch-p branch)
    (let ((subselector
           (avl-rem-branch-selector branch)))
      (and
       (avl-rem-selection-possible
        subselector left-sequence)
       (avl-rem-left-selection-continuation-p
        selector subselector
        left-sequence datum right-sequence))))
   (t
    (let ((subselector
           (avl-rem-branch-selector branch)))
      (and
       (avl-rem-selection-possible
        subselector right-sequence)
       (avl-rem-right-selection-continuation-p
        selector subselector
        left-sequence datum right-sequence))))))

(defun avl-rem-result-conclusion-p
    (selector t3 result split)
  (and
   (equal
    (avl-rem-sequence result)
    (append
     (avl-rem-split-left split)
     (avl-rem-split-right split)))
   (and
    (avl-rem-selected selector split)
    (equal
     (avl-rem-rebuild split)
     (avl-rem-sequence t3)))
   (avl-rem-height-drop-one-p
    (avl-rem-height t3)
    (avl-rem-height result))))

;; Left recursive branch: all split, recursive-tree, and rebuilt-tree
;; variables retain their source universal quantifier scopes.

(defun-sk avl-rem-left-result-obligation-p
    (selector t3 tree-left datum tree-right
              subselector split new-left)
  (forall (result)
    (implies
     (avl-rem-t2-p result)
     (implies
      (and
       (equal
        (avl-rem-sequence result)
        (avl-rem-node-model
         (avl-rem-sequence new-left)
         datum
         (avl-rem-sequence tree-right)))
       (avl-rem-near-node-height-exact-if-balanced-p
        new-left tree-right result))
      (avl-rem-result-conclusion-p
       selector
       t3
       result
       (avl-rem-right-extend
        split datum
        (avl-rem-sequence tree-right)))))))

(defun-sk avl-rem-left-recursive-obligations-p
    (selector t3 tree-left datum tree-right subselector)
  (forall (split new-left)
    (implies
     (and
      (avl-rem-split-p split)
      (avl-rem-t2-p new-left))
     (implies
      (and
       (and
        (avl-rem-selected subselector split)
        (equal
         (avl-rem-rebuild split)
         (avl-rem-sequence tree-left)))
       (equal
        (avl-rem-sequence new-left)
        (append
         (avl-rem-split-left split)
         (avl-rem-split-right split)))
       (avl-rem-height-drop-one-p
        (avl-rem-height tree-left)
        (avl-rem-height new-left)))
      (and
       (let ((difference
              (- (avl-rem-height new-left)
                 (avl-rem-height tree-right))))
         (and
          (<=
           (- (- (avl-rem-balancing)) 1)
           difference)
          (<=
           difference
           (+ (avl-rem-balancing) 1))))
       (avl-rem-left-result-obligation-p
        selector t3 tree-left datum tree-right
        subselector split new-left))))))

(defun avl-rem-left-conclusion-p
    (selector t3 tree-left datum tree-right subselector)
  (and
   (and
    (and
     (<= 0 (avl-rem-height t3))
     (<
      (avl-rem-height tree-left)
      (avl-rem-height t3)))
    (avl-rem-selection-possible
     subselector
     (avl-rem-sequence tree-left)))
   (avl-rem-left-recursive-obligations-p
    selector t3 tree-left datum tree-right subselector)))

;; Right recursive branch, symmetric to the source's Left branch.

(defun-sk avl-rem-right-result-obligation-p
    (selector t3 tree-left datum tree-right
              subselector split new-right)
  (forall (result)
    (implies
     (avl-rem-t2-p result)
     (implies
      (and
       (equal
        (avl-rem-sequence result)
        (avl-rem-node-model
         (avl-rem-sequence tree-left)
         datum
         (avl-rem-sequence new-right)))
       (avl-rem-near-node-height-exact-if-balanced-p
        tree-left new-right result))
      (avl-rem-result-conclusion-p
       selector
       t3
       result
       (avl-rem-left-extend
        (avl-rem-sequence tree-left)
        datum split))))))

(defun-sk avl-rem-right-recursive-obligations-p
    (selector t3 tree-left datum tree-right subselector)
  (forall (split new-right)
    (implies
     (and
      (avl-rem-split-p split)
      (avl-rem-t2-p new-right))
     (implies
      (and
       (and
        (avl-rem-selected subselector split)
        (equal
         (avl-rem-rebuild split)
         (avl-rem-sequence tree-right)))
       (equal
        (avl-rem-sequence new-right)
        (append
         (avl-rem-split-left split)
         (avl-rem-split-right split)))
       (avl-rem-height-drop-one-p
        (avl-rem-height tree-right)
        (avl-rem-height new-right)))
      (and
       (let ((difference
              (- (avl-rem-height tree-left)
                 (avl-rem-height new-right))))
         (and
          (<=
           (- (- (avl-rem-balancing)) 1)
           difference)
          (<=
           difference
           (+ (avl-rem-balancing) 1))))
       (avl-rem-right-result-obligation-p
        selector t3 tree-left datum tree-right
        subselector split new-right))))))

(defun avl-rem-right-conclusion-p
    (selector t3 tree-left datum tree-right subselector)
  (and
   (and
    (and
     (<= 0 (avl-rem-height t3))
     (<
      (avl-rem-height tree-right)
      (avl-rem-height t3)))
    (avl-rem-selection-possible
     subselector
     (avl-rem-sequence tree-right)))
   (avl-rem-right-recursive-obligations-p
    selector t3 tree-left datum tree-right subselector)))

;; Root-selection branch.

(defun-sk avl-rem-here-result-obligation-p
    (selector t3 tree-left datum tree-right)
  (forall (result)
    (implies
     (avl-rem-t2-p result)
     (implies
      (and
       (equal
        (avl-rem-sequence result)
        (append
         (avl-rem-sequence tree-left)
         (avl-rem-sequence tree-right)))
       (avl-rem-near-node-height-p
        tree-left tree-right result))
      (avl-rem-result-conclusion-p
       selector
       t3
       result
       (avl-rem-split
        (avl-rem-sequence tree-left)
        (avl-rem-some datum)
        (avl-rem-sequence tree-right)))))))

(defun avl-rem-here-conclusion-p
    (selector t3 tree-left datum tree-right)
  (and
   (avl-rem-within-balance-p
    (avl-rem-height tree-left)
    (avl-rem-height tree-right))
   (avl-rem-here-result-obligation-p
    selector t3 tree-left datum tree-right)))

(defun avl-rem-part-conclusion-p
    (branch selector t3 tree-left datum tree-right)
  (cond
   ((avl-rem-left-branch-p branch)
    (avl-rem-left-conclusion-p
     selector t3 tree-left datum tree-right
     (avl-rem-branch-selector branch)))
   ((avl-rem-right-branch-p branch)
    (avl-rem-right-conclusion-p
     selector t3 tree-left datum tree-right
     (avl-rem-branch-selector branch)))
   (t
    (avl-rem-here-conclusion-p
     selector t3 tree-left datum tree-right))))

(defun-sk avl-rem-all-parts-obligation-p
    (selector t3 tree-left datum tree-right)
  (forall (branch)
    (implies
     (avl-rem-part-base-p branch)
     (implies
      (avl-rem-part-premise-p
       branch selector
       (avl-rem-sequence tree-left)
       datum
       (avl-rem-sequence tree-right))
      (avl-rem-part-conclusion-p
       branch selector t3
       tree-left datum tree-right)))))

(defun avl-rem-node-conclusion-p
    (selector t3 tree-left datum tree-right)
  (let ((left-sequence
         (avl-rem-sequence tree-left))
        (right-sequence
         (avl-rem-sequence tree-right)))
    (and
     (and
      (avl-rem-selection-possible
       selector
       (avl-rem-node-model
        left-sequence datum right-sequence))
      (equal
       (avl-rem-aggregate
        (avl-rem-sequence tree-left))
       (avl-rem-aggregate left-sequence))
      (equal
       (avl-rem-aggregate
        (avl-rem-sequence tree-right))
       (avl-rem-aggregate right-sequence)))
     (avl-rem-all-parts-obligation-p
      selector t3 tree-left datum tree-right))))

(defun avl-rem-conclusion-p (selector t3 view)
  (if (avl-rem-view-empty-p view)
      (avl-rem-empty-conclusion-p selector t3)
    (avl-rem-node-conclusion-p
     selector
     t3
     (avl-rem-view-left view)
     (avl-rem-view-datum view)
     (avl-rem-view-right view))))

(defun-sk ntp4vc-pearl-avl-avl-removeqtvc-statement ()
  (forall (selector t3 view)
    (implies
     (and
      (avl-rem-selector-p selector)
      (avl-rem-t2-p t3)
      (avl-rem-view-p view))
     (implies
      (and
       (avl-rem-background-p)
       (avl-rem-selection-possible
        selector
        (avl-rem-sequence t3))
       (avl-rem-view-fact-p view t3))
      (avl-rem-conclusion-p
       selector t3 view)))))

(value-triple :itpeval-statement-checked)
:q
