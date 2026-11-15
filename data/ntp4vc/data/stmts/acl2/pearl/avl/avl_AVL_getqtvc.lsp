;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_getqtvc: the AVL lookup verification condition for
;; selector-guided splitting of empty and internal-node sequence models.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the arbitrary source carriers t, t1 alpha,
;; t2 alpha, selector, and part at a fixed arbitrary inhabited alpha.

(defstub avl-get-t-p (x) t)
(defstub avl-get-t1-p (x) t)
(defstub avl-get-t2-p (x) t)
(defstub avl-get-selector-p (x) t)
(defstub avl-get-part-p (x) t)

(defstub avl-get-zero () t)
(defstub avl-get-op (left right) t)
(defstub avl-get-measure (datum) t)
(defstub avl-get-measure-closure (datum) t)
(defstub avl-get-aggregate (sequence) t)
(defstub avl-get-balancing () t)
(defstub avl-get-repr (object) t)
(defstub avl-get-m1 (object) t)
(defstub avl-get-selected (selector split) t)
(defstub avl-get-selection-possible (selector sequence) t)

(defun avl-get-t1-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (avl-get-t1-p (car xs))
     (avl-get-t1-list-p (cdr xs)))))

;; Empty trees are NIL. Nodes are exact records
;; (:TREE-NODE left datum right height summary).

(defun avl-get-tree-empty-p (tree)
  (equal tree nil))

(defun avl-get-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun avl-get-tree-left (tree)
  (cadr tree))

(defun avl-get-tree-datum (tree)
  (caddr tree))

(defun avl-get-tree-right (tree)
  (cadddr tree))

(defun avl-get-tree-height (tree)
  (car (cddddr tree)))

(defun avl-get-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avl-get-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-get-tree-empty-p tree)
      t
    (and
     (avl-get-tree-node-shape-p tree)
     (avl-get-tree-p (avl-get-tree-left tree))
     (avl-get-t1-p (avl-get-tree-datum tree))
     (avl-get-tree-p (avl-get-tree-right tree))
     (natp (avl-get-tree-height tree))
     (avl-get-t-p (avl-get-tree-summary tree)))))

;; The source model record m is represented exactly as
;; (:M sequence integer-height).

(defun avl-get-m-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (avl-get-t1-list-p (cadr model))
   (integerp (caddr model))))

(defun avl-get-m-seq (model)
  (cadr model))

(defun avl-get-m-hgt (model)
  (caddr model))

(defun avl-get-node-model (left datum right)
  (append left (cons datum right)))

(defun avl-get-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-get-tree-empty-p tree)
      nil
    (if (avl-get-tree-node-shape-p tree)
        (avl-get-node-model
         (avl-get-seq-model (avl-get-tree-left tree))
         (avl-get-tree-datum tree)
         (avl-get-seq-model (avl-get-tree-right tree)))
      nil)))

(defun avl-get-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-get-tree-empty-p tree)
      0
    (if (avl-get-tree-node-shape-p tree)
        (let ((left-height
               (avl-get-real-height
                (avl-get-tree-left tree)))
              (right-height
               (avl-get-real-height
                (avl-get-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avl-get-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-get-tree-empty-p tree)
      t
    (if (avl-get-tree-node-shape-p tree)
        (let* ((left (avl-get-tree-left tree))
               (right (avl-get-tree-right tree))
               (height (avl-get-tree-height tree))
               (summary (avl-get-tree-summary tree))
               (difference
                (- (avl-get-real-height right)
                   (avl-get-real-height left))))
          (and
           (equal height (avl-get-real-height tree))
           (equal
            summary
            (avl-get-aggregate
             (avl-get-seq-model tree)))
           (<= (- (avl-get-balancing)) difference)
           (<= difference (avl-get-balancing))
           (avl-get-balanced-p left)
           (avl-get-balanced-p right)))
      nil)))

;; Empty views are NIL. Nodes are exact records
;; (:VIEW-NODE left datum right height summary).

(defun avl-get-view-empty-p (view)
  (equal view nil))

(defun avl-get-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun avl-get-view-left (view)
  (cadr view))

(defun avl-get-view-datum (view)
  (caddr view))

(defun avl-get-view-right (view)
  (cadddr view))

(defun avl-get-view-height (view)
  (car (cddddr view)))

(defun avl-get-view-summary (view)
  (cadr (cddddr view)))

(defun avl-get-view-p (view)
  (or
   (avl-get-view-empty-p view)
   (and
    (avl-get-view-node-shape-p view)
    (avl-get-t2-p (avl-get-view-left view))
    (avl-get-t1-p (avl-get-view-datum view))
    (avl-get-t2-p (avl-get-view-right view))
    (natp (avl-get-view-height view))
    (avl-get-t-p (avl-get-view-summary view)))))

;; Options, splits, and selector-directed branches are exact tagged
;; representations of the source datatypes.

(defun avl-get-none ()
  (list :none))

(defun avl-get-some (datum)
  (list :some datum))

(defun avl-get-option-p (option)
  (or
   (equal option (avl-get-none))
   (and
    (true-listp option)
    (equal (len option) 2)
    (equal (car option) :some)
    (avl-get-t1-p (cadr option)))))

(defun avl-get-option-to-seq (option)
  (if (equal option (avl-get-none))
      nil
    (list (cadr option))))

(defun avl-get-split (left middle right)
  (list :split left middle right))

(defun avl-get-split-p (split)
  (and
   (true-listp split)
   (equal (len split) 4)
   (equal (car split) :split)
   (avl-get-t1-list-p (cadr split))
   (avl-get-option-p (caddr split))
   (avl-get-t1-list-p (cadddr split))))

(defun avl-get-split-left (split)
  (cadr split))

(defun avl-get-split-middle (split)
  (caddr split))

(defun avl-get-split-right (split)
  (cadddr split))

(defun avl-get-rebuild (split)
  (append
   (append
    (avl-get-split-left split)
    (avl-get-option-to-seq
     (avl-get-split-middle split)))
   (avl-get-split-right split)))

(defun avl-get-left-extend (left datum split)
  (avl-get-split
   (append
    left
    (cons datum
          (avl-get-split-left split)))
   (avl-get-split-middle split)
   (avl-get-split-right split)))

(defun avl-get-right-extend (split datum right)
  (avl-get-split
   (avl-get-split-left split)
   (avl-get-split-middle split)
   (append
    (avl-get-split-right split)
    (cons datum right))))

(defun avl-get-here ()
  (list :here))

(defun avl-get-left-branch (selector)
  (list :left selector))

(defun avl-get-right-branch (selector)
  (list :right selector))

(defun avl-get-part-base-p (branch)
  (or
   (equal branch (avl-get-here))
   (and
    (true-listp branch)
    (equal (len branch) 2)
    (or
     (equal (car branch) :left)
     (equal (car branch) :right))
    (avl-get-selector-p (cadr branch)))))

(defun avl-get-left-branch-p (branch)
  (and
   (consp branch)
   (equal (car branch) :left)))

(defun avl-get-right-branch-p (branch)
  (and
   (consp branch)
   (equal (car branch) :right)))

(defun avl-get-branch-selector (branch)
  (cadr branch))

;; The source theory's carrier nonemptiness, typing, monoid and aggregation
;; laws, positive balance bound, representation invariant, injectivity, and
;; empty-selection law remain explicit assumptions of the statement.

(defun-sk avl-get-carriers-inhabited-p ()
  (exists (datum object selector part)
    (and
     (avl-get-t1-p datum)
     (avl-get-t2-p object)
     (avl-get-selector-p selector)
     (avl-get-part-p part))))

(defun-sk avl-get-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avl-get-t-p left)
       (avl-get-t-p right))
      (avl-get-t-p
       (avl-get-op left right)))
     (implies
      (avl-get-t1-p datum)
      (and
       (avl-get-t-p
        (avl-get-measure datum))
       (avl-get-t-p
        (avl-get-measure-closure datum))))
     (implies
      (avl-get-t1-list-p sequence)
      (avl-get-t-p
       (avl-get-aggregate sequence)))
     (implies
      (avl-get-t2-p object)
      (and
       (avl-get-tree-p
        (avl-get-repr object))
       (avl-get-m-p
        (avl-get-m1 object)))))))

(defun-sk avl-get-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avl-get-t-p a)
      (avl-get-t-p b)
      (avl-get-t-p c))
     (equal
      (avl-get-op a (avl-get-op b c))
      (avl-get-op (avl-get-op a b) c)))))

(defun-sk avl-get-neutral-p ()
  (forall (x)
    (implies
     (avl-get-t-p x)
     (and
      (equal
       (avl-get-op x (avl-get-zero))
       x)
      (equal
       x
       (avl-get-op (avl-get-zero) x))))))

(defun-sk avl-get-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avl-get-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avl-get-aggregate sequence)
      (avl-get-measure-closure
       (car sequence))))))

(defun-sk avl-get-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avl-get-t1-list-p left)
      (avl-get-t1-list-p right))
     (equal
      (avl-get-aggregate
       (append left right))
      (avl-get-op
       (avl-get-aggregate left)
       (avl-get-aggregate right))))))

(defun-sk avl-get-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avl-get-t1-p datum)
     (equal
      (avl-get-measure-closure datum)
      (avl-get-measure datum)))))

(defun-sk avl-get-invariant-p ()
  (forall (object)
    (implies
     (avl-get-t2-p object)
     (let ((tree (avl-get-repr object))
           (model (avl-get-m1 object)))
       (and
        (avl-get-balanced-p tree)
        (equal
         (avl-get-m-seq model)
         (avl-get-seq-model tree))
        (equal
         (avl-get-m-hgt model)
         (avl-get-real-height tree)))))))

(defun-sk avl-get-t2-injective-p ()
  (forall (left right)
    (implies
     (and
      (avl-get-t2-p left)
      (avl-get-t2-p right)
      (equal
       (avl-get-repr left)
       (avl-get-repr right))
      (equal
       (avl-get-m1 left)
       (avl-get-m1 right)))
     (equal left right))))

(defun-sk avl-get-selection-empty-law-p ()
  (forall (selector)
    (implies
     (avl-get-selector-p selector)
     (implies
      (avl-get-selection-possible selector nil)
      (avl-get-selected
       selector
       (avl-get-split
        nil
        (avl-get-none)
        nil))))))

(defun avl-get-background-p ()
  (and
   (avl-get-t-p (avl-get-zero))
   (natp (avl-get-balancing))
   (< 0 (avl-get-balancing))
   (avl-get-carriers-inhabited-p)
   (avl-get-function-closures-p)
   (avl-get-associative-p)
   (avl-get-neutral-p)
   (equal
    (avl-get-aggregate nil)
    (avl-get-zero))
   (avl-get-aggregate-singleton-law-p)
   (avl-get-aggregate-concatenation-law-p)
   (avl-get-measure-closure-law-p)
   (avl-get-invariant-p)
   (avl-get-t2-injective-p)
   (avl-get-selection-empty-law-p)))

(defun avl-get-sequence (object)
  (avl-get-m-seq
   (avl-get-m1 object)))

(defun avl-get-height (object)
  (avl-get-m-hgt
   (avl-get-m1 object)))

(defun avl-get-max (left right)
  (if (< left right)
      right
    left))

(defun avl-get-within-balance-p (left-height right-height)
  (let ((difference (- left-height right-height)))
    (and
     (<= (- (avl-get-balancing)) difference)
     (<= difference (avl-get-balancing)))))

;; This is the complete second theorem premise, including both view cases.

(defun avl-get-view-fact-p (view t3)
  (if (avl-get-view-empty-p view)
      (and
       (equal (avl-get-height t3) 0)
       (equal (avl-get-sequence t3) nil))
    (let* ((left (avl-get-view-left view))
           (datum (avl-get-view-datum view))
           (right (avl-get-view-right view))
           (height (avl-get-view-height view))
           (summary (avl-get-view-summary view)))
      (and
       (equal
        (avl-get-sequence t3)
        (avl-get-node-model
         (avl-get-sequence left)
         datum
         (avl-get-sequence right)))
       (equal
        summary
        (avl-get-aggregate
         (avl-get-sequence t3)))
       (avl-get-within-balance-p
        (avl-get-height left)
        (avl-get-height right))
       (equal
        (avl-get-height t3)
        height)
       (equal
        height
        (+ 1
           (avl-get-max
            (avl-get-height left)
            (avl-get-height right))))))))

(defun avl-get-empty-conclusion-p (selector t3)
  (let ((empty-split
         (avl-get-split
          nil
          (avl-get-none)
          nil)))
    (and
     (and
      (avl-get-selected selector empty-split)
      (equal
       (avl-get-rebuild empty-split)
       (avl-get-sequence t3)))
     (equal
      (avl-get-split-middle empty-split)
      (avl-get-none)))))

;; These predicates preserve the universal split continuations appearing in
;; the Left and Right premises of the selector branch case.

(defun-sk avl-get-left-premise-continuation-p
    (selector subselector left-sequence datum right-sequence)
  (forall (split)
    (implies
     (avl-get-split-p split)
     (implies
      (and
       (avl-get-selected subselector split)
       (equal
        (avl-get-rebuild split)
        left-sequence))
      (avl-get-selected
       selector
       (avl-get-right-extend
        split datum right-sequence))))))

(defun-sk avl-get-right-premise-continuation-p
    (selector subselector left-sequence datum right-sequence)
  (forall (split)
    (implies
     (avl-get-split-p split)
     (implies
      (and
       (avl-get-selected subselector split)
       (equal
        (avl-get-rebuild split)
        right-sequence))
      (avl-get-selected
       selector
       (avl-get-left-extend
        left-sequence datum split))))))

(defun avl-get-part-premise-p
    (branch selector left-sequence datum right-sequence)
  (cond
   ((equal branch (avl-get-here))
    (avl-get-selected
     selector
     (avl-get-split
      left-sequence
      (avl-get-some datum)
      right-sequence)))
   ((avl-get-left-branch-p branch)
    (let ((subselector
           (avl-get-branch-selector branch)))
      (and
       (avl-get-selection-possible
        subselector left-sequence)
       (avl-get-left-premise-continuation-p
        selector subselector
        left-sequence datum right-sequence))))
   (t
    (let ((subselector
           (avl-get-branch-selector branch)))
      (and
       (avl-get-selection-possible
        subselector right-sequence)
       (avl-get-right-premise-continuation-p
        selector subselector
        left-sequence datum right-sequence))))))

(defun avl-get-middle-matches-p (split option)
  (if (equal option (avl-get-none))
      (equal
       (avl-get-split-middle split)
       (avl-get-none))
    (equal
     (avl-get-split-middle split)
     (avl-get-some (cadr option)))))

;; Left and Right conclusions retain the source universal quantifiers over
;; every split r and every option res.

(defun-sk avl-get-left-result-obligation-p
    (selector t3 tree-left datum tree-right subselector)
  (forall (split option)
    (implies
     (and
      (avl-get-split-p split)
      (avl-get-option-p option))
     (implies
      (and
       (and
        (avl-get-selected subselector split)
        (equal
         (avl-get-rebuild split)
         (avl-get-sequence tree-left)))
       (avl-get-middle-matches-p
        split option))
      (let ((extended
             (avl-get-right-extend
              split datum
              (avl-get-sequence tree-right))))
        (and
         (and
          (avl-get-selected selector extended)
          (equal
           (avl-get-rebuild extended)
           (avl-get-sequence t3)))
         (avl-get-middle-matches-p
          extended option)))))))

(defun-sk avl-get-right-result-obligation-p
    (selector t3 tree-left datum tree-right subselector)
  (forall (split option)
    (implies
     (and
      (avl-get-split-p split)
      (avl-get-option-p option))
     (implies
      (and
       (and
        (avl-get-selected subselector split)
        (equal
         (avl-get-rebuild split)
         (avl-get-sequence tree-right)))
       (avl-get-middle-matches-p
        split option))
      (let ((extended
             (avl-get-left-extend
              (avl-get-sequence tree-left)
              datum split)))
        (and
         (and
          (avl-get-selected selector extended)
          (equal
           (avl-get-rebuild extended)
           (avl-get-sequence t3)))
         (avl-get-middle-matches-p
          extended option)))))))

(defun avl-get-left-conclusion-p
    (selector t3 tree-left datum tree-right subselector)
  (and
   (and
    (and
     (<= 0 (avl-get-height t3))
     (<
      (avl-get-height tree-left)
      (avl-get-height t3)))
    (avl-get-selection-possible
     subselector
     (avl-get-sequence tree-left)))
   (avl-get-left-result-obligation-p
    selector t3 tree-left datum tree-right subselector)))

(defun avl-get-right-conclusion-p
    (selector t3 tree-left datum tree-right subselector)
  (and
   (and
    (and
     (<= 0 (avl-get-height t3))
     (<
      (avl-get-height tree-right)
      (avl-get-height t3)))
    (avl-get-selection-possible
     subselector
     (avl-get-sequence tree-right)))
   (avl-get-right-result-obligation-p
    selector t3 tree-left datum tree-right subselector)))

(defun avl-get-here-conclusion-p
    (selector t3 tree-left datum tree-right)
  (let ((root-split
         (avl-get-split
          (avl-get-sequence tree-left)
          (avl-get-some datum)
          (avl-get-sequence tree-right))))
    (and
     (and
      (avl-get-selected selector root-split)
      (equal
       (avl-get-rebuild root-split)
       (avl-get-sequence t3)))
     (equal
      (avl-get-split-middle root-split)
      (avl-get-some datum)))))

(defun avl-get-part-conclusion-p
    (branch selector t3 tree-left datum tree-right)
  (cond
   ((avl-get-left-branch-p branch)
    (avl-get-left-conclusion-p
     selector t3 tree-left datum tree-right
     (avl-get-branch-selector branch)))
   ((avl-get-right-branch-p branch)
    (avl-get-right-conclusion-p
     selector t3 tree-left datum tree-right
     (avl-get-branch-selector branch)))
   (t
    (avl-get-here-conclusion-p
     selector t3 tree-left datum tree-right))))

(defun-sk avl-get-all-parts-obligation-p
    (selector t3 tree-left datum tree-right)
  (forall (branch)
    (implies
     (avl-get-part-base-p branch)
     (implies
      (avl-get-part-premise-p
       branch selector
       (avl-get-sequence tree-left)
       datum
       (avl-get-sequence tree-right))
      (avl-get-part-conclusion-p
       branch selector t3
       tree-left datum tree-right)))))

(defun avl-get-node-conclusion-p
    (selector t3 tree-left datum tree-right)
  (let ((left-sequence
         (avl-get-sequence tree-left))
        (right-sequence
         (avl-get-sequence tree-right)))
    (and
     (and
      (avl-get-selection-possible
       selector
       (avl-get-node-model
        left-sequence datum right-sequence))
      (equal
       (avl-get-aggregate
        (avl-get-sequence tree-left))
       (avl-get-aggregate left-sequence))
      (equal
       (avl-get-aggregate
        (avl-get-sequence tree-right))
       (avl-get-aggregate right-sequence)))
     (avl-get-all-parts-obligation-p
      selector t3 tree-left datum tree-right))))

(defun avl-get-conclusion-p (selector t3 view)
  (if (avl-get-view-empty-p view)
      (avl-get-empty-conclusion-p selector t3)
    (avl-get-node-conclusion-p
     selector
     t3
     (avl-get-view-left view)
     (avl-get-view-datum view)
     (avl-get-view-right view))))

(defun-sk ntp4vc-pearl-avl-avl-getqtvc-statement ()
  (forall (selector t3 view)
    (implies
     (and
      (avl-get-selector-p selector)
      (avl-get-t2-p t3)
      (avl-get-view-p view))
     (implies
      (and
       (avl-get-background-p)
       (avl-get-selection-possible
        selector
        (avl-get-sequence t3))
       (avl-get-view-fact-p view t3))
      (avl-get-conclusion-p
       selector t3 view)))))

(value-triple :itpeval-statement-checked)
:q
