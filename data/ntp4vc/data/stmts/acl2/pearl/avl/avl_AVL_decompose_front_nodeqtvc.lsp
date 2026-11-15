;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_decompose_front_nodeqtvc: the AVL decompose-front-node
;; verification condition for sequence decomposition and bounded height change.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces for the abstract carriers t, t1 alpha, and
;; t2 alpha at an arbitrary inhabited alpha.

(defstub avl-dfn-t-p (x) t)
(defstub avl-dfn-t1-p (x) t)
(defstub avl-dfn-t2-p (x) t)

(defstub avl-dfn-zero () t)
(defstub avl-dfn-op (left right) t)
(defstub avl-dfn-measure (datum) t)
(defstub avl-dfn-measure-closure (datum) t)
(defstub avl-dfn-aggregate (sequence) t)
(defstub avl-dfn-balancing () t)
(defstub avl-dfn-repr (object) t)
(defstub avl-dfn-m1 (object) t)

(defun avl-dfn-t1-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (avl-dfn-t1-p (car xs))
     (avl-dfn-t1-list-p (cdr xs)))))

;; Empty trees are NIL. Nodes are exact records
;; (:TREE-NODE left datum right height summary).

(defun avl-dfn-tree-empty-p (tree)
  (equal tree nil))

(defun avl-dfn-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun avl-dfn-tree-left (tree)
  (cadr tree))

(defun avl-dfn-tree-datum (tree)
  (caddr tree))

(defun avl-dfn-tree-right (tree)
  (cadddr tree))

(defun avl-dfn-tree-height (tree)
  (car (cddddr tree)))

(defun avl-dfn-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avl-dfn-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-dfn-tree-empty-p tree)
      t
    (and
     (avl-dfn-tree-node-shape-p tree)
     (avl-dfn-tree-p (avl-dfn-tree-left tree))
     (avl-dfn-t1-p (avl-dfn-tree-datum tree))
     (avl-dfn-tree-p (avl-dfn-tree-right tree))
     (natp (avl-dfn-tree-height tree))
     (avl-dfn-t-p (avl-dfn-tree-summary tree)))))

;; The source record m is represented as (:M sequence height).

(defun avl-dfn-m-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (avl-dfn-t1-list-p (cadr model))
   (integerp (caddr model))))

(defun avl-dfn-m-seq (model)
  (cadr model))

(defun avl-dfn-m-hgt (model)
  (caddr model))

(defun avl-dfn-node-model (left datum right)
  (append left (cons datum right)))

(defun avl-dfn-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-dfn-tree-empty-p tree)
      nil
    (if (avl-dfn-tree-node-shape-p tree)
        (avl-dfn-node-model
         (avl-dfn-seq-model (avl-dfn-tree-left tree))
         (avl-dfn-tree-datum tree)
         (avl-dfn-seq-model (avl-dfn-tree-right tree)))
      nil)))

(defun avl-dfn-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-dfn-tree-empty-p tree)
      0
    (if (avl-dfn-tree-node-shape-p tree)
        (let ((left-height
               (avl-dfn-real-height
                (avl-dfn-tree-left tree)))
              (right-height
               (avl-dfn-real-height
                (avl-dfn-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avl-dfn-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-dfn-tree-empty-p tree)
      t
    (if (avl-dfn-tree-node-shape-p tree)
        (let* ((left (avl-dfn-tree-left tree))
               (right (avl-dfn-tree-right tree))
               (height (avl-dfn-tree-height tree))
               (summary (avl-dfn-tree-summary tree))
               (difference
                (- (avl-dfn-real-height right)
                   (avl-dfn-real-height left))))
          (and
           (equal height (avl-dfn-real-height tree))
           (equal
            summary
            (avl-dfn-aggregate
             (avl-dfn-seq-model tree)))
           (<= (- (avl-dfn-balancing)) difference)
           (<= difference (avl-dfn-balancing))
           (avl-dfn-balanced-p left)
           (avl-dfn-balanced-p right)))
      nil)))

;; Empty views are NIL. Nodes are exact records
;; (:VIEW-NODE left datum right height summary).

(defun avl-dfn-view-empty-p (view)
  (equal view nil))

(defun avl-dfn-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun avl-dfn-view-left (view)
  (cadr view))

(defun avl-dfn-view-datum (view)
  (caddr view))

(defun avl-dfn-view-right (view)
  (cadddr view))

(defun avl-dfn-view-height (view)
  (car (cddddr view)))

(defun avl-dfn-view-summary (view)
  (cadr (cddddr view)))

(defun avl-dfn-view-p (view)
  (or
   (avl-dfn-view-empty-p view)
   (and
    (avl-dfn-view-node-shape-p view)
    (avl-dfn-t2-p (avl-dfn-view-left view))
    (avl-dfn-t1-p (avl-dfn-view-datum view))
    (avl-dfn-t2-p (avl-dfn-view-right view))
    (natp (avl-dfn-view-height view))
    (avl-dfn-t-p (avl-dfn-view-summary view)))))

;; The source theory's carrier nonemptiness, typing, monoid and aggregation
;; laws, positive balance bound, invariant, and injectivity remain explicit
;; assumptions of the statement.

(defun-sk avl-dfn-carriers-inhabited-p ()
  (exists (datum object)
    (and
     (avl-dfn-t1-p datum)
     (avl-dfn-t2-p object))))

(defun-sk avl-dfn-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avl-dfn-t-p left)
       (avl-dfn-t-p right))
      (avl-dfn-t-p
       (avl-dfn-op left right)))
     (implies
      (avl-dfn-t1-p datum)
      (and
       (avl-dfn-t-p
        (avl-dfn-measure datum))
       (avl-dfn-t-p
        (avl-dfn-measure-closure datum))))
     (implies
      (avl-dfn-t1-list-p sequence)
      (avl-dfn-t-p
       (avl-dfn-aggregate sequence)))
     (implies
      (avl-dfn-t2-p object)
      (and
       (avl-dfn-tree-p
        (avl-dfn-repr object))
       (avl-dfn-m-p
        (avl-dfn-m1 object)))))))

(defun-sk avl-dfn-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avl-dfn-t-p a)
      (avl-dfn-t-p b)
      (avl-dfn-t-p c))
     (equal
      (avl-dfn-op a (avl-dfn-op b c))
      (avl-dfn-op (avl-dfn-op a b) c)))))

(defun-sk avl-dfn-neutral-p ()
  (forall (x)
    (implies
     (avl-dfn-t-p x)
     (and
      (equal
       (avl-dfn-op x (avl-dfn-zero))
       x)
      (equal
       x
       (avl-dfn-op (avl-dfn-zero) x))))))

(defun-sk avl-dfn-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avl-dfn-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avl-dfn-aggregate sequence)
      (avl-dfn-measure-closure
       (car sequence))))))

(defun-sk avl-dfn-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avl-dfn-t1-list-p left)
      (avl-dfn-t1-list-p right))
     (equal
      (avl-dfn-aggregate
       (append left right))
      (avl-dfn-op
       (avl-dfn-aggregate left)
       (avl-dfn-aggregate right))))))

(defun-sk avl-dfn-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avl-dfn-t1-p datum)
     (equal
      (avl-dfn-measure-closure datum)
      (avl-dfn-measure datum)))))

(defun-sk avl-dfn-invariant-p ()
  (forall (object)
    (implies
     (avl-dfn-t2-p object)
     (let ((tree (avl-dfn-repr object))
           (model (avl-dfn-m1 object)))
       (and
        (avl-dfn-balanced-p tree)
        (equal
         (avl-dfn-m-seq model)
         (avl-dfn-seq-model tree))
        (equal
         (avl-dfn-m-hgt model)
         (avl-dfn-real-height tree)))))))

(defun-sk avl-dfn-t2-injective-p ()
  (forall (left right)
    (implies
     (and
      (avl-dfn-t2-p left)
      (avl-dfn-t2-p right)
      (equal
       (avl-dfn-repr left)
       (avl-dfn-repr right))
      (equal
       (avl-dfn-m1 left)
       (avl-dfn-m1 right)))
     (equal left right))))

(defun avl-dfn-background-p ()
  (and
   (avl-dfn-t-p (avl-dfn-zero))
   (natp (avl-dfn-balancing))
   (< 0 (avl-dfn-balancing))
   (avl-dfn-carriers-inhabited-p)
   (avl-dfn-function-closures-p)
   (avl-dfn-associative-p)
   (avl-dfn-neutral-p)
   (equal
    (avl-dfn-aggregate nil)
    (avl-dfn-zero))
   (avl-dfn-aggregate-singleton-law-p)
   (avl-dfn-aggregate-concatenation-law-p)
   (avl-dfn-measure-closure-law-p)
   (avl-dfn-invariant-p)
   (avl-dfn-t2-injective-p)))

(defun avl-dfn-sequence (object)
  (avl-dfn-m-seq
   (avl-dfn-m1 object)))

(defun avl-dfn-height (object)
  (avl-dfn-m-hgt
   (avl-dfn-m1 object)))

(defun avl-dfn-max (left right)
  (if (< left right) right left))

(defun avl-dfn-within-balance-p (left-height right-height)
  (let ((difference (- left-height right-height)))
    (and
     (<= (- (avl-dfn-balancing)) difference)
     (<= difference (avl-dfn-balancing)))))

(defun avl-dfn-height-loss-bounded-p (left right result)
  (let* ((expected-height
          (+ 1
             (avl-dfn-max
              (avl-dfn-height left)
              (avl-dfn-height right))))
         (height-loss
          (- expected-height
             (avl-dfn-height result))))
    (and
     (<= 0 height-loss)
     (<= height-loss 1))))

(defun avl-dfn-height-exact-if-balanced-p (left right result)
  (let ((expected-height
         (+ 1
            (avl-dfn-max
             (avl-dfn-height left)
             (avl-dfn-height right)))))
    (and
     (avl-dfn-height-loss-bounded-p left right result)
     (implies
      (avl-dfn-within-balance-p
       (avl-dfn-height left)
       (avl-dfn-height right))
      (equal
       expected-height
       (avl-dfn-height result))))))

;; This is the source fact2, including the complete AEmpty/ANode case split.

(defun avl-dfn-view-fact-p (view l)
  (if (avl-dfn-view-empty-p view)
      (and
       (equal (avl-dfn-height l) 0)
       (equal (avl-dfn-sequence l) nil))
    (let* ((left (avl-dfn-view-left view))
           (datum (avl-dfn-view-datum view))
           (right (avl-dfn-view-right view))
           (height (avl-dfn-view-height view))
           (summary (avl-dfn-view-summary view))
           (left-height (avl-dfn-height left))
           (right-height (avl-dfn-height right)))
      (and
       (equal
        (avl-dfn-sequence l)
        (avl-dfn-node-model
         (avl-dfn-sequence left)
         datum
         (avl-dfn-sequence right)))
       (equal
        summary
        (avl-dfn-aggregate
         (avl-dfn-sequence l)))
       (avl-dfn-within-balance-p
        left-height right-height)
       (equal (avl-dfn-height l) height)
       (equal
        height
        (+ 1
           (avl-dfn-max
            left-height right-height)))))))

;; The first node-branch continuation retains its universal d3 and left1.

(defun-sk avl-dfn-left-continuation-p (r view)
  (forall (d3 left1)
    (implies
     (and
      (avl-dfn-t1-p d3)
      (avl-dfn-t2-p left1))
     (implies
      (and
       (equal
        (avl-dfn-node-model
         (avl-dfn-sequence
          (avl-dfn-view-left view))
         (avl-dfn-view-datum view)
         (avl-dfn-sequence
          (avl-dfn-view-right view)))
        (cons
         d3
         (avl-dfn-sequence left1)))
       (avl-dfn-height-loss-bounded-p
        (avl-dfn-view-left view)
        (avl-dfn-view-right view)
        left1))
      (let ((difference
             (- (avl-dfn-height left1)
                (avl-dfn-height r))))
        (and
         (<=
          (- (- (avl-dfn-balancing)) 1)
          difference)
         (<=
          difference
          (+ (avl-dfn-balancing) 1))))))))

(defun avl-dfn-first-conclusion-p (l r view)
  (if (avl-dfn-view-empty-p view)
      t
    (and
     (and
      (<= 0 (avl-dfn-height l))
      (<
       (avl-dfn-height
        (avl-dfn-view-left view))
       (avl-dfn-height l)))
     (avl-dfn-within-balance-p
      (avl-dfn-height
       (avl-dfn-view-left view))
      (avl-dfn-height
       (avl-dfn-view-right view)))
     (avl-dfn-left-continuation-p r view))))

;; The intermediate res1 witness remains existentially quantified inside the
;; node-branch premise of the universal result continuation.

(defun-sk avl-dfn-node-result-premise-p
    (result-datum result r d view)
  (exists (res1)
    (and
     (avl-dfn-t2-p res1)
     (equal
      (avl-dfn-node-model
       (avl-dfn-sequence
        (avl-dfn-view-left view))
       (avl-dfn-view-datum view)
       (avl-dfn-sequence
        (avl-dfn-view-right view)))
      (cons
       result-datum
       (avl-dfn-sequence res1)))
     (avl-dfn-height-loss-bounded-p
      (avl-dfn-view-left view)
      (avl-dfn-view-right view)
      res1)
     (equal
      (avl-dfn-sequence result)
      (avl-dfn-node-model
       (avl-dfn-sequence res1)
       d
       (avl-dfn-sequence r)))
     (avl-dfn-height-exact-if-balanced-p
      res1 r result))))

(defun avl-dfn-result-premise-p
    (result-datum result r d view)
  (if (avl-dfn-view-empty-p view)
      (and
       (equal result-datum d)
       (equal result r))
    (avl-dfn-node-result-premise-p
     result-datum result r d view)))

(defun-sk avl-dfn-result-continuation-p (l r d view)
  (forall (result-datum result)
    (implies
     (and
      (avl-dfn-t1-p result-datum)
      (avl-dfn-t2-p result))
     (implies
      (avl-dfn-result-premise-p
       result-datum result r d view)
      (and
       (equal
        (avl-dfn-node-model
         (avl-dfn-sequence l)
         d
         (avl-dfn-sequence r))
        (cons
         result-datum
         (avl-dfn-sequence result)))
       (avl-dfn-height-loss-bounded-p
        l r result))))))

(defun-sk
    ntp4vc-pearl-avl-avl-decompose-front-nodeqtvc-statement ()
  (forall (l r view d)
    (implies
     (and
      (avl-dfn-background-p)
      (avl-dfn-t2-p l)
      (avl-dfn-t2-p r)
      (avl-dfn-view-p view)
      (avl-dfn-t1-p d))
     (implies
      (and
       (<=
        (- (avl-dfn-balancing))
        (- (avl-dfn-height l)
           (avl-dfn-height r)))
       (<=
        (- (avl-dfn-height l)
           (avl-dfn-height r))
        (avl-dfn-balancing))
       (avl-dfn-view-fact-p view l))
      (and
       (avl-dfn-first-conclusion-p l r view)
       (avl-dfn-result-continuation-p
        l r d view))))))

(value-triple :itpeval-statement-checked)
:q
