;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_decompose_back_nodeqtvc: the AVL decompose-back-node
;; verification condition for sequence decomposition and bounded height change.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces for the abstract carriers t, t1 alpha, and
;; t2 alpha at an arbitrary inhabited alpha.

(defstub avl-dbn-t-p (x) t)
(defstub avl-dbn-t1-p (x) t)
(defstub avl-dbn-t2-p (x) t)

(defstub avl-dbn-zero () t)
(defstub avl-dbn-op (left right) t)
(defstub avl-dbn-measure (datum) t)
(defstub avl-dbn-measure-closure (datum) t)
(defstub avl-dbn-aggregate (sequence) t)
(defstub avl-dbn-balancing () t)
(defstub avl-dbn-repr (object) t)
(defstub avl-dbn-m1 (object) t)

(defun avl-dbn-t1-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (avl-dbn-t1-p (car xs))
     (avl-dbn-t1-list-p (cdr xs)))))

;; Empty trees are NIL. Nodes are exact records
;; (:TREE-NODE left datum right height summary).

(defun avl-dbn-tree-empty-p (tree)
  (equal tree nil))

(defun avl-dbn-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun avl-dbn-tree-left (tree)
  (cadr tree))

(defun avl-dbn-tree-datum (tree)
  (caddr tree))

(defun avl-dbn-tree-right (tree)
  (cadddr tree))

(defun avl-dbn-tree-height (tree)
  (car (cddddr tree)))

(defun avl-dbn-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avl-dbn-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-dbn-tree-empty-p tree)
      t
    (and
     (avl-dbn-tree-node-shape-p tree)
     (avl-dbn-tree-p (avl-dbn-tree-left tree))
     (avl-dbn-t1-p (avl-dbn-tree-datum tree))
     (avl-dbn-tree-p (avl-dbn-tree-right tree))
     (natp (avl-dbn-tree-height tree))
     (avl-dbn-t-p (avl-dbn-tree-summary tree)))))

;; The source record m is represented as (:M sequence height).

(defun avl-dbn-m-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (avl-dbn-t1-list-p (cadr model))
   (integerp (caddr model))))

(defun avl-dbn-m-seq (model)
  (cadr model))

(defun avl-dbn-m-hgt (model)
  (caddr model))

(defun avl-dbn-node-model (left datum right)
  (append left (cons datum right)))

(defun avl-dbn-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-dbn-tree-empty-p tree)
      nil
    (if (avl-dbn-tree-node-shape-p tree)
        (avl-dbn-node-model
         (avl-dbn-seq-model (avl-dbn-tree-left tree))
         (avl-dbn-tree-datum tree)
         (avl-dbn-seq-model (avl-dbn-tree-right tree)))
      nil)))

(defun avl-dbn-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-dbn-tree-empty-p tree)
      0
    (if (avl-dbn-tree-node-shape-p tree)
        (let ((left-height
               (avl-dbn-real-height
                (avl-dbn-tree-left tree)))
              (right-height
               (avl-dbn-real-height
                (avl-dbn-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avl-dbn-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-dbn-tree-empty-p tree)
      t
    (if (avl-dbn-tree-node-shape-p tree)
        (let* ((left (avl-dbn-tree-left tree))
               (right (avl-dbn-tree-right tree))
               (height (avl-dbn-tree-height tree))
               (summary (avl-dbn-tree-summary tree))
               (difference
                (- (avl-dbn-real-height right)
                   (avl-dbn-real-height left))))
          (and
           (equal height (avl-dbn-real-height tree))
           (equal
            summary
            (avl-dbn-aggregate
             (avl-dbn-seq-model tree)))
           (<= (- (avl-dbn-balancing)) difference)
           (<= difference (avl-dbn-balancing))
           (avl-dbn-balanced-p left)
           (avl-dbn-balanced-p right)))
      nil)))

;; Empty views are NIL. Nodes are exact records
;; (:VIEW-NODE left datum right height summary).

(defun avl-dbn-view-empty-p (view)
  (equal view nil))

(defun avl-dbn-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun avl-dbn-view-left (view)
  (cadr view))

(defun avl-dbn-view-datum (view)
  (caddr view))

(defun avl-dbn-view-right (view)
  (cadddr view))

(defun avl-dbn-view-height (view)
  (car (cddddr view)))

(defun avl-dbn-view-summary (view)
  (cadr (cddddr view)))

(defun avl-dbn-view-p (view)
  (or
   (avl-dbn-view-empty-p view)
   (and
    (avl-dbn-view-node-shape-p view)
    (avl-dbn-t2-p (avl-dbn-view-left view))
    (avl-dbn-t1-p (avl-dbn-view-datum view))
    (avl-dbn-t2-p (avl-dbn-view-right view))
    (natp (avl-dbn-view-height view))
    (avl-dbn-t-p (avl-dbn-view-summary view)))))

;; The source theory's carrier nonemptiness, typing, monoid and aggregation
;; laws, positive balance bound, invariant, and injectivity remain explicit
;; assumptions of the statement.

(defun-sk avl-dbn-carriers-inhabited-p ()
  (exists (datum object)
    (and
     (avl-dbn-t1-p datum)
     (avl-dbn-t2-p object))))

(defun-sk avl-dbn-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avl-dbn-t-p left)
       (avl-dbn-t-p right))
      (avl-dbn-t-p
       (avl-dbn-op left right)))
     (implies
      (avl-dbn-t1-p datum)
      (and
       (avl-dbn-t-p
        (avl-dbn-measure datum))
       (avl-dbn-t-p
        (avl-dbn-measure-closure datum))))
     (implies
      (avl-dbn-t1-list-p sequence)
      (avl-dbn-t-p
       (avl-dbn-aggregate sequence)))
     (implies
      (avl-dbn-t2-p object)
      (and
       (avl-dbn-tree-p
        (avl-dbn-repr object))
       (avl-dbn-m-p
        (avl-dbn-m1 object)))))))

(defun-sk avl-dbn-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avl-dbn-t-p a)
      (avl-dbn-t-p b)
      (avl-dbn-t-p c))
     (equal
      (avl-dbn-op a (avl-dbn-op b c))
      (avl-dbn-op (avl-dbn-op a b) c)))))

(defun-sk avl-dbn-neutral-p ()
  (forall (x)
    (implies
     (avl-dbn-t-p x)
     (and
      (equal
       (avl-dbn-op x (avl-dbn-zero))
       x)
      (equal
       x
       (avl-dbn-op (avl-dbn-zero) x))))))

(defun-sk avl-dbn-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avl-dbn-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avl-dbn-aggregate sequence)
      (avl-dbn-measure-closure
       (car sequence))))))

(defun-sk avl-dbn-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avl-dbn-t1-list-p left)
      (avl-dbn-t1-list-p right))
     (equal
      (avl-dbn-aggregate
       (append left right))
      (avl-dbn-op
       (avl-dbn-aggregate left)
       (avl-dbn-aggregate right))))))

(defun-sk avl-dbn-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avl-dbn-t1-p datum)
     (equal
      (avl-dbn-measure-closure datum)
      (avl-dbn-measure datum)))))

(defun-sk avl-dbn-invariant-p ()
  (forall (object)
    (implies
     (avl-dbn-t2-p object)
     (let ((tree (avl-dbn-repr object))
           (model (avl-dbn-m1 object)))
       (and
        (avl-dbn-balanced-p tree)
        (equal
         (avl-dbn-m-seq model)
         (avl-dbn-seq-model tree))
        (equal
         (avl-dbn-m-hgt model)
         (avl-dbn-real-height tree)))))))

(defun-sk avl-dbn-t2-injective-p ()
  (forall (left right)
    (implies
     (and
      (avl-dbn-t2-p left)
      (avl-dbn-t2-p right)
      (equal
       (avl-dbn-repr left)
       (avl-dbn-repr right))
      (equal
       (avl-dbn-m1 left)
       (avl-dbn-m1 right)))
     (equal left right))))

(defun avl-dbn-background-p ()
  (and
   (avl-dbn-t-p (avl-dbn-zero))
   (natp (avl-dbn-balancing))
   (< 0 (avl-dbn-balancing))
   (avl-dbn-carriers-inhabited-p)
   (avl-dbn-function-closures-p)
   (avl-dbn-associative-p)
   (avl-dbn-neutral-p)
   (equal
    (avl-dbn-aggregate nil)
    (avl-dbn-zero))
   (avl-dbn-aggregate-singleton-law-p)
   (avl-dbn-aggregate-concatenation-law-p)
   (avl-dbn-measure-closure-law-p)
   (avl-dbn-invariant-p)
   (avl-dbn-t2-injective-p)))

(defun avl-dbn-sequence (object)
  (avl-dbn-m-seq
   (avl-dbn-m1 object)))

(defun avl-dbn-height (object)
  (avl-dbn-m-hgt
   (avl-dbn-m1 object)))

(defun avl-dbn-max (left right)
  (if (< left right) right left))

(defun avl-dbn-within-balance-p (left-height right-height)
  (let ((difference (- left-height right-height)))
    (and
     (<= (- (avl-dbn-balancing)) difference)
     (<= difference (avl-dbn-balancing)))))

(defun avl-dbn-height-loss-bounded-p (left right result)
  (let* ((expected-height
          (+ 1
             (avl-dbn-max
              (avl-dbn-height left)
              (avl-dbn-height right))))
         (height-loss
          (- expected-height
             (avl-dbn-height result))))
    (and
     (<= 0 height-loss)
     (<= height-loss 1))))

(defun avl-dbn-height-exact-if-balanced-p (left right result)
  (let ((expected-height
         (+ 1
            (avl-dbn-max
             (avl-dbn-height left)
             (avl-dbn-height right)))))
    (and
     (avl-dbn-height-loss-bounded-p left right result)
     (implies
      (avl-dbn-within-balance-p
       (avl-dbn-height left)
       (avl-dbn-height right))
      (equal
       expected-height
       (avl-dbn-height result))))))

;; This is the source fact2, including the complete AEmpty/ANode case split.

(defun avl-dbn-view-fact-p (view r)
  (if (avl-dbn-view-empty-p view)
      (and
       (equal (avl-dbn-height r) 0)
       (equal (avl-dbn-sequence r) nil))
    (let* ((left (avl-dbn-view-left view))
           (datum (avl-dbn-view-datum view))
           (right (avl-dbn-view-right view))
           (height (avl-dbn-view-height view))
           (summary (avl-dbn-view-summary view))
           (left-height (avl-dbn-height left))
           (right-height (avl-dbn-height right)))
      (and
       (equal
        (avl-dbn-sequence r)
        (avl-dbn-node-model
         (avl-dbn-sequence left)
         datum
         (avl-dbn-sequence right)))
       (equal
        summary
        (avl-dbn-aggregate
         (avl-dbn-sequence r)))
       (avl-dbn-within-balance-p
        left-height right-height)
       (equal (avl-dbn-height r) height)
       (equal
        height
        (+ 1
           (avl-dbn-max
            left-height right-height)))))))

;; The first node-branch continuation retains its universal right1 and d3.

(defun-sk avl-dbn-right-continuation-p (l view)
  (forall (right1 d3)
    (implies
     (and
      (avl-dbn-t2-p right1)
      (avl-dbn-t1-p d3))
     (implies
      (and
       (equal
        (avl-dbn-node-model
         (avl-dbn-sequence
          (avl-dbn-view-left view))
         (avl-dbn-view-datum view)
         (avl-dbn-sequence
          (avl-dbn-view-right view)))
        (append
         (avl-dbn-sequence right1)
         (list d3)))
       (avl-dbn-height-loss-bounded-p
        (avl-dbn-view-left view)
        (avl-dbn-view-right view)
        right1))
      (let ((difference
             (- (avl-dbn-height l)
                (avl-dbn-height right1))))
        (and
         (<=
          (- (- (avl-dbn-balancing)) 1)
          difference)
         (<=
          difference
          (+ (avl-dbn-balancing) 1))))))))

(defun avl-dbn-first-conclusion-p (l r view)
  (if (avl-dbn-view-empty-p view)
      t
    (and
     (and
      (<= 0 (avl-dbn-height r))
      (<
       (avl-dbn-height
        (avl-dbn-view-right view))
       (avl-dbn-height r)))
     (avl-dbn-within-balance-p
      (avl-dbn-height
       (avl-dbn-view-left view))
      (avl-dbn-height
       (avl-dbn-view-right view)))
     (avl-dbn-right-continuation-p l view))))

;; The intermediate res1 witness remains existentially quantified inside the
;; node-branch premise of the universal result continuation.

(defun-sk avl-dbn-node-result-premise-p
    (result result-datum l d view)
  (exists (res1)
    (and
     (avl-dbn-t2-p res1)
     (equal
      (avl-dbn-node-model
       (avl-dbn-sequence
        (avl-dbn-view-left view))
       (avl-dbn-view-datum view)
       (avl-dbn-sequence
        (avl-dbn-view-right view)))
      (append
       (avl-dbn-sequence res1)
       (list result-datum)))
     (avl-dbn-height-loss-bounded-p
      (avl-dbn-view-left view)
      (avl-dbn-view-right view)
      res1)
     (equal
      (avl-dbn-sequence result)
      (avl-dbn-node-model
       (avl-dbn-sequence l)
       d
       (avl-dbn-sequence res1)))
     (avl-dbn-height-exact-if-balanced-p
      l res1 result))))

(defun avl-dbn-result-premise-p
    (result result-datum l d view)
  (if (avl-dbn-view-empty-p view)
      (and
       (equal result l)
       (equal result-datum d))
    (avl-dbn-node-result-premise-p
     result result-datum l d view)))

(defun-sk avl-dbn-result-continuation-p (l r d view)
  (forall (result result-datum)
    (implies
     (and
      (avl-dbn-t2-p result)
      (avl-dbn-t1-p result-datum))
     (implies
      (avl-dbn-result-premise-p
       result result-datum l d view)
      (and
       (equal
        (avl-dbn-node-model
         (avl-dbn-sequence l)
         d
         (avl-dbn-sequence r))
        (append
         (avl-dbn-sequence result)
         (list result-datum)))
       (avl-dbn-height-loss-bounded-p
        l r result))))))

(defun-sk
    ntp4vc-pearl-avl-avl-decompose-back-nodeqtvc-statement ()
  (forall (l r view d)
    (implies
     (and
      (avl-dbn-background-p)
      (avl-dbn-t2-p l)
      (avl-dbn-t2-p r)
      (avl-dbn-view-p view)
      (avl-dbn-t1-p d))
     (implies
      (and
       (<=
        (- (avl-dbn-balancing))
        (- (avl-dbn-height l)
           (avl-dbn-height r)))
       (<=
        (- (avl-dbn-height l)
           (avl-dbn-height r))
        (avl-dbn-balancing))
       (avl-dbn-view-fact-p view r))
      (and
       (avl-dbn-first-conclusion-p l r view)
       (avl-dbn-result-continuation-p
        l r d view))))))

(value-triple :itpeval-statement-checked)
:q
