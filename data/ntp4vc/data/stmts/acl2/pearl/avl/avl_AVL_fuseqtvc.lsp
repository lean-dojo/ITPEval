;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_fuseqtvc: the AVL fuse verification condition for
;; concatenated sequence models and bounded height change.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the arbitrary source carriers t, t1 alpha,
;; and t2 alpha at a fixed arbitrary inhabited alpha.

(defstub avlf-t-p (x) t)
(defstub avlf-t1-p (x) t)
(defstub avlf-t2-p (x) t)

(defstub avlf-zero () t)
(defstub avlf-op (left right) t)
(defstub avlf-measure (datum) t)
(defstub avlf-measure-closure (datum) t)
(defstub avlf-aggregate (sequence) t)
(defstub avlf-balancing () t)
(defstub avlf-repr (object) t)
(defstub avlf-m1 (object) t)

(defun avlf-t1-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (avlf-t1-p (car xs))
     (avlf-t1-list-p (cdr xs)))))

;; Empty trees are NIL. Nodes are exact records
;; (:TREE-NODE left datum right height summary).

(defun avlf-tree-empty-p (tree)
  (equal tree nil))

(defun avlf-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun avlf-tree-left (tree)
  (cadr tree))

(defun avlf-tree-datum (tree)
  (caddr tree))

(defun avlf-tree-right (tree)
  (cadddr tree))

(defun avlf-tree-height (tree)
  (car (cddddr tree)))

(defun avlf-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avlf-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlf-tree-empty-p tree)
      t
    (and
     (avlf-tree-node-shape-p tree)
     (avlf-tree-p (avlf-tree-left tree))
     (avlf-t1-p (avlf-tree-datum tree))
     (avlf-tree-p (avlf-tree-right tree))
     (natp (avlf-tree-height tree))
     (avlf-t-p (avlf-tree-summary tree)))))

;; The source model record m is represented as (:M sequence height).

(defun avlf-m-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (avlf-t1-list-p (cadr model))
   (integerp (caddr model))))

(defun avlf-m-seq (model)
  (cadr model))

(defun avlf-m-hgt (model)
  (caddr model))

(defun avlf-node-model (left datum right)
  (append left (cons datum right)))

(defun avlf-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlf-tree-empty-p tree)
      nil
    (if (avlf-tree-node-shape-p tree)
        (avlf-node-model
         (avlf-seq-model (avlf-tree-left tree))
         (avlf-tree-datum tree)
         (avlf-seq-model (avlf-tree-right tree)))
      nil)))

(defun avlf-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlf-tree-empty-p tree)
      0
    (if (avlf-tree-node-shape-p tree)
        (let ((left-height
               (avlf-real-height
                (avlf-tree-left tree)))
              (right-height
               (avlf-real-height
                (avlf-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avlf-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlf-tree-empty-p tree)
      t
    (if (avlf-tree-node-shape-p tree)
        (let* ((left (avlf-tree-left tree))
               (right (avlf-tree-right tree))
               (height (avlf-tree-height tree))
               (summary (avlf-tree-summary tree))
               (difference
                (- (avlf-real-height right)
                   (avlf-real-height left))))
          (and
           (equal height (avlf-real-height tree))
           (equal
            summary
            (avlf-aggregate
             (avlf-seq-model tree)))
           (<= (- (avlf-balancing)) difference)
           (<= difference (avlf-balancing))
           (avlf-balanced-p left)
           (avlf-balanced-p right)))
      nil)))

;; Empty views are NIL. Nodes are exact records
;; (:VIEW-NODE left datum right height summary).

(defun avlf-view-empty-p (view)
  (equal view nil))

(defun avlf-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun avlf-view-left (view)
  (cadr view))

(defun avlf-view-datum (view)
  (caddr view))

(defun avlf-view-right (view)
  (cadddr view))

(defun avlf-view-height (view)
  (car (cddddr view)))

(defun avlf-view-summary (view)
  (cadr (cddddr view)))

(defun avlf-view-p (view)
  (or
   (avlf-view-empty-p view)
   (and
    (avlf-view-node-shape-p view)
    (avlf-t2-p (avlf-view-left view))
    (avlf-t1-p (avlf-view-datum view))
    (avlf-t2-p (avlf-view-right view))
    (natp (avlf-view-height view))
    (avlf-t-p (avlf-view-summary view)))))

;; The source theory's carrier nonemptiness, typing, monoid and aggregation
;; laws, positive balance bound, representation invariant, and injectivity
;; remain explicit assumptions of the statement.

(defun-sk avlf-carriers-inhabited-p ()
  (exists (datum object)
    (and
     (avlf-t1-p datum)
     (avlf-t2-p object))))

(defun-sk avlf-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avlf-t-p left)
       (avlf-t-p right))
      (avlf-t-p
       (avlf-op left right)))
     (implies
      (avlf-t1-p datum)
      (and
       (avlf-t-p
        (avlf-measure datum))
       (avlf-t-p
        (avlf-measure-closure datum))))
     (implies
      (avlf-t1-list-p sequence)
      (avlf-t-p
       (avlf-aggregate sequence)))
     (implies
      (avlf-t2-p object)
      (and
       (avlf-tree-p
        (avlf-repr object))
       (avlf-m-p
        (avlf-m1 object)))))))

(defun-sk avlf-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avlf-t-p a)
      (avlf-t-p b)
      (avlf-t-p c))
     (equal
      (avlf-op a (avlf-op b c))
      (avlf-op (avlf-op a b) c)))))

(defun-sk avlf-neutral-p ()
  (forall (x)
    (implies
     (avlf-t-p x)
     (and
      (equal
       (avlf-op x (avlf-zero))
       x)
      (equal
       x
       (avlf-op (avlf-zero) x))))))

(defun-sk avlf-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avlf-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avlf-aggregate sequence)
      (avlf-measure-closure
       (car sequence))))))

(defun-sk avlf-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avlf-t1-list-p left)
      (avlf-t1-list-p right))
     (equal
      (avlf-aggregate
       (append left right))
      (avlf-op
       (avlf-aggregate left)
       (avlf-aggregate right))))))

(defun-sk avlf-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avlf-t1-p datum)
     (equal
      (avlf-measure-closure datum)
      (avlf-measure datum)))))

(defun-sk avlf-invariant-p ()
  (forall (object)
    (implies
     (avlf-t2-p object)
     (let ((tree (avlf-repr object))
           (model (avlf-m1 object)))
       (and
        (avlf-balanced-p tree)
        (equal
         (avlf-m-seq model)
         (avlf-seq-model tree))
        (equal
         (avlf-m-hgt model)
         (avlf-real-height tree)))))))

(defun-sk avlf-t2-injective-p ()
  (forall (left right)
    (implies
     (and
      (avlf-t2-p left)
      (avlf-t2-p right)
      (equal
       (avlf-repr left)
       (avlf-repr right))
      (equal
       (avlf-m1 left)
       (avlf-m1 right)))
     (equal left right))))

(defun avlf-background-p ()
  (and
   (avlf-t-p (avlf-zero))
   (natp (avlf-balancing))
   (< 0 (avlf-balancing))
   (avlf-carriers-inhabited-p)
   (avlf-function-closures-p)
   (avlf-associative-p)
   (avlf-neutral-p)
   (equal
    (avlf-aggregate nil)
    (avlf-zero))
   (avlf-aggregate-singleton-law-p)
   (avlf-aggregate-concatenation-law-p)
   (avlf-measure-closure-law-p)
   (avlf-invariant-p)
   (avlf-t2-injective-p)))

(defun avlf-sequence (object)
  (avlf-m-seq
   (avlf-m1 object)))

(defun avlf-height (object)
  (avlf-m-hgt
   (avlf-m1 object)))

(defun avlf-max (left right)
  (if (< left right)
      right
    left))

(defun avlf-within-balance-p (left-height right-height)
  (let ((difference (- left-height right-height)))
    (and
     (<= (- (avlf-balancing)) difference)
     (<= difference (avlf-balancing)))))

(defun avlf-near-node-height-p (left right result)
  (let* ((expected
          (+ 1
             (avlf-max
              (avlf-height left)
              (avlf-height right))))
         (height-loss
          (- expected
             (avlf-height result))))
    (and
     (<= 0 height-loss)
     (<= height-loss 1))))

(defun avlf-near-node-height-exact-if-balanced-p
    (left right result)
  (let* ((left-height (avlf-height left))
         (right-height (avlf-height right))
         (expected
          (+ 1
             (avlf-max
              left-height right-height)))
         (height-loss
          (- expected
             (avlf-height result))))
    (and
     (<= 0 height-loss)
     (<= height-loss 1)
     (implies
      (avlf-within-balance-p
       left-height right-height)
      (equal
       expected
       (avlf-height result))))))

;; This is the source view premise for either input tree, including the full
;; AEmpty/ANode case split.

(defun avlf-view-fact-p (view object)
  (if (avlf-view-empty-p view)
      (and
       (equal (avlf-height object) 0)
       (equal (avlf-sequence object) nil))
    (let* ((left (avlf-view-left view))
           (datum (avlf-view-datum view))
           (right (avlf-view-right view))
           (height (avlf-view-height view))
           (summary (avlf-view-summary view))
           (left-height (avlf-height left))
           (right-height (avlf-height right)))
      (and
       (equal
        (avlf-sequence object)
        (avlf-node-model
         (avlf-sequence left)
         datum
         (avlf-sequence right)))
       (equal
        summary
        (avlf-aggregate
         (avlf-sequence object)))
       (avlf-within-balance-p
        left-height right-height)
       (equal (avlf-height object) height)
       (equal
        height
        (+ 1
           (avlf-max
            left-height right-height)))))))

;; The first node branch keeps the source universal d0 and r' continuation.

(defun-sk avlf-right-tail-obligation-p (l view)
  (forall (d0 rprime)
    (implies
     (and
      (avlf-t1-p d0)
      (avlf-t2-p rprime))
     (implies
      (and
       (equal
        (avlf-node-model
         (avlf-sequence
          (avlf-view-left view))
         (avlf-view-datum view)
         (avlf-sequence
          (avlf-view-right view)))
        (cons
         d0
         (avlf-sequence rprime)))
       (avlf-near-node-height-p
        (avlf-view-left view)
        (avlf-view-right view)
        rprime))
      (let ((difference
             (- (avlf-height l)
                (avlf-height rprime))))
        (and
         (<=
          (- (- (avlf-balancing)) 1)
          difference)
         (<=
          difference
          (+ (avlf-balancing) 1))))))))

(defun avlf-right-view-conclusion-p (l view)
  (if (avlf-view-empty-p view)
      t
    (and
     (avlf-within-balance-p
      (avlf-height
       (avlf-view-left view))
      (avlf-height
       (avlf-view-right view)))
     (avlf-right-tail-obligation-p
      l view))))

(defun-sk avlf-first-conclusion-p (l r o1)
  (forall (o2)
    (implies
     (avlf-view-p o2)
     (implies
      (avlf-view-fact-p o2 r)
      (avlf-right-view-conclusion-p
       l o2)))))

(defun avlf-operational-conclusion-p (l r o1)
  (if (avlf-view-empty-p o1)
      t
    (avlf-first-conclusion-p
     l r o1)))

;; The witnesses o2, d2, and res remain existential and internal to the node
;; premise of the universal result continuation.

(defun-sk avlf-right-node-result-p (result l view)
  (exists (d2 res)
    (and
     (avlf-t1-p d2)
     (avlf-t2-p res)
     (and
      (equal
       (avlf-node-model
        (avlf-sequence
         (avlf-view-left view))
        (avlf-view-datum view)
        (avlf-sequence
         (avlf-view-right view)))
       (cons
        d2
        (avlf-sequence res)))
      (avlf-near-node-height-p
       (avlf-view-left view)
       (avlf-view-right view)
       res))
     (equal
      (avlf-sequence result)
      (avlf-node-model
       (avlf-sequence l)
       d2
       (avlf-sequence res)))
     (avlf-near-node-height-exact-if-balanced-p
      l res result))))

(defun avlf-right-result-p (result l view)
  (if (avlf-view-empty-p view)
      (equal result l)
    (avlf-right-node-result-p
     result l view)))

(defun-sk avlf-left-node-result-premise-p
    (result l r)
  (exists (o2)
    (and
     (avlf-view-p o2)
     (avlf-view-fact-p o2 r)
     (avlf-right-result-p
      result l o2))))

(defun avlf-result-premise-p (result l r o1)
  (if (avlf-view-empty-p o1)
      (equal result r)
    (avlf-left-node-result-premise-p
     result l r)))

(defun avlf-final-result-p (result l r)
  (let* ((expected
          (+ 1
             (avlf-max
              (avlf-height l)
              (avlf-height r))))
         (height-loss
          (- expected
             (avlf-height result))))
    (and
     (equal
      (avlf-sequence result)
      (append
       (avlf-sequence l)
       (avlf-sequence r)))
     (<= height-loss 1)
     (<= 0 height-loss))))

(defun-sk avlf-result-continuation-p (l r o1)
  (forall (result)
    (implies
     (avlf-t2-p result)
     (implies
      (avlf-result-premise-p
       result l r o1)
      (avlf-final-result-p
       result l r)))))

(defun-sk ntp4vc-pearl-avl-avl-fuseqtvc-statement ()
  (forall (l r o1)
    (implies
     (and
      (avlf-background-p)
      (avlf-t2-p l)
      (avlf-t2-p r)
      (avlf-view-p o1))
     (implies
      (and
       (<=
        (- (avlf-balancing))
        (- (avlf-height l)
           (avlf-height r)))
       (<=
        (- (avlf-height l)
           (avlf-height r))
        (avlf-balancing))
       (avlf-view-fact-p o1 l))
      (and
       (avlf-operational-conclusion-p
        l r o1)
       (avlf-result-continuation-p
        l r o1))))))

(value-triple :itpeval-statement-checked)
:q
