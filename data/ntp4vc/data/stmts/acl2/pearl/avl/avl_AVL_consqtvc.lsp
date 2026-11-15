;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_consqtvc: the AVL cons verification condition relating
;; sequence models, stored and real heights, balance bounds, and recursive results.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative recognizers retain the arbitrary source carriers t, t1 alpha,
;; and t2 alpha.  The fixed source operations remain arbitrary functions whose
;; typing and algebraic laws are explicit assumptions of the statement.

(defstub avlc-t-recognizer (x) t)
(defstub avlc-t1-recognizer (x) t)
(defstub avlc-t2-recognizer (x) t)
(defstub avlc-zero () t)
(defstub avlc-op (left right) t)
(defstub avlc-measure (datum) t)
(defstub avlc-balancing () t)
(defstub avlc-repr (object) t)
(defstub avlc-m1 (object) t)

(defun avlc-t-p (x)
  (if (avlc-t-recognizer x) t nil))

(defun avlc-t1-p (x)
  (if (avlc-t1-recognizer x) t nil))

(defun avlc-t2-p (x)
  (if (avlc-t2-recognizer x) t nil))

(defun avlc-t1-list-p (xs)
  (if (consp xs)
      (and
       (avlc-t1-p (car xs))
       (avlc-t1-list-p (cdr xs)))
    (equal xs nil)))

;; The source record m has a sequence field and an integer height field.

(defun avlc-m (sequence height)
  (list :avlc-m sequence height))

(defun avlc-m-p (object)
  (and
   (true-listp object)
   (equal (len object) 3)
   (equal (car object) :avlc-m)
   (avlc-t1-list-p (cadr object))
   (integerp (caddr object))))

(defun avlc-m-seq (object)
  (cadr object))

(defun avlc-m-hgt (object)
  (caddr object))

;; Tagged finite trees are a faithful ACL2 representation of the source
;; inductive tree datatype.

(defun avlc-empty ()
  (list :avlc-empty))

(defun avlc-node (left datum right height summary)
  (list :avlc-node left datum right height summary))

(defun avlc-tree-empty-p (tree)
  (equal tree (avlc-empty)))

(defun avlc-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :avlc-node)))

(defun avlc-tree-left (tree)
  (cadr tree))

(defun avlc-tree-datum (tree)
  (caddr tree))

(defun avlc-tree-right (tree)
  (cadddr tree))

(defun avlc-tree-height (tree)
  (car (cddddr tree)))

(defun avlc-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avlc-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlc-tree-empty-p tree)
      t
    (and
     (avlc-tree-node-shape-p tree)
     (avlc-tree-p (avlc-tree-left tree))
     (avlc-t1-p (avlc-tree-datum tree))
     (avlc-tree-p (avlc-tree-right tree))
     (natp (avlc-tree-height tree))
     (avlc-t-p (avlc-tree-summary tree)))))

(defun avlc-node-model (left datum right)
  (append left (cons datum right)))

(defun avlc-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlc-tree-empty-p tree)
      nil
    (if (avlc-tree-node-shape-p tree)
        (avlc-node-model
         (avlc-seq-model (avlc-tree-left tree))
         (avlc-tree-datum tree)
         (avlc-seq-model (avlc-tree-right tree)))
      nil)))

(defun avlc-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlc-tree-empty-p tree)
      0
    (if (avlc-tree-node-shape-p tree)
        (let ((left-height
               (avlc-real-height (avlc-tree-left tree)))
              (right-height
               (avlc-real-height (avlc-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

;; For the only function argument used by this VC, agg is uniquely determined
;; by agg_empty, agg_sing, agg_cat, associativity, and the neutral element.

(defun avlc-aggregate-measure (sequence)
  (if (endp sequence)
      (avlc-zero)
    (avlc-op
     (avlc-measure (car sequence))
     (avlc-aggregate-measure (cdr sequence)))))

(defun avlc-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlc-tree-empty-p tree)
      t
    (if (avlc-tree-node-shape-p tree)
        (let* ((left (avlc-tree-left tree))
               (right (avlc-tree-right tree))
               (left-height (avlc-real-height left))
               (right-height (avlc-real-height right))
               (difference (- right-height left-height))
               (bound (avlc-balancing)))
          (and
           (equal (avlc-tree-height tree)
                  (avlc-real-height tree))
           (equal (avlc-tree-summary tree)
                  (avlc-aggregate-measure
                   (avlc-seq-model tree)))
           (<= (- bound) difference)
           (<= difference bound)
           (avlc-balanced-p left)
           (avlc-balanced-p right)))
      nil)))

;; The source Inhabited instances for t1 alpha and t2 alpha are retained as
;; explicit carrier-nonemptiness assumptions.

(defun-sk avlc-carriers-inhabited-p ()
  (exists (datum object)
    (and
     (avlc-t1-p datum)
     (avlc-t2-p object))))

;; Universal closures of the source typing, monoid, invariant, and injectivity
;; assumptions for the arbitrary carriers and operations.

(defun-sk avlc-operation-types-p ()
  (forall (x y)
    (and
     (implies
      (and
       (avlc-t-p x)
       (avlc-t-p y))
      (avlc-t-p (avlc-op x y)))
     (implies
      (avlc-t1-p x)
      (avlc-t-p (avlc-measure x)))
     (implies
      (avlc-t1-list-p x)
      (avlc-t-p
       (avlc-aggregate-measure x)))
     (implies
      (avlc-t2-p x)
      (and
       (avlc-tree-p (avlc-repr x))
       (avlc-m-p (avlc-m1 x)))))))

(defun-sk avlc-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avlc-t-p a)
      (avlc-t-p b)
      (avlc-t-p c))
     (equal
      (avlc-op a (avlc-op b c))
      (avlc-op (avlc-op a b) c)))))

(defun-sk avlc-neutral-p ()
  (forall (x)
    (implies
     (avlc-t-p x)
     (and
      (equal
       (avlc-op x (avlc-zero))
       x)
      (equal
       x
       (avlc-op (avlc-zero) x))))))

(defun-sk avlc-t-invariant-p ()
  (forall (self)
    (implies
     (avlc-t2-p self)
     (and
      (avlc-balanced-p (avlc-repr self))
      (equal
       (avlc-m-seq (avlc-m1 self))
       (avlc-seq-model (avlc-repr self)))
      (equal
       (avlc-m-hgt (avlc-m1 self))
       (avlc-real-height (avlc-repr self)))))))

(defun-sk avlc-t-injective-p ()
  (forall (left right)
    (implies
     (and
      (avlc-t2-p left)
      (avlc-t2-p right)
      (equal
       (avlc-repr left)
       (avlc-repr right))
      (equal
       (avlc-m1 left)
       (avlc-m1 right)))
     (equal left right))))

;; Tagged values retain the source view datatype and all field types.

(defun avlc-aempty ()
  (list :avlc-aempty))

(defun avlc-anode (left datum right height summary)
  (list :avlc-anode left datum right height summary))

(defun avlc-view-empty-p (view)
  (equal view (avlc-aempty)))

(defun avlc-view-node-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :avlc-anode)
   (avlc-t2-p (cadr view))
   (avlc-t1-p (caddr view))
   (avlc-t2-p (cadddr view))
   (natp (car (cddddr view)))
   (avlc-t-p (cadr (cddddr view)))))

(defun avlc-view-p (view)
  (or
   (avlc-view-empty-p view)
   (avlc-view-node-p view)))

(defun avlc-view-left (view)
  (cadr view))

(defun avlc-view-datum (view)
  (caddr view))

(defun avlc-view-right (view)
  (cadddr view))

(defun avlc-view-height (view)
  (car (cddddr view)))

(defun avlc-view-summary (view)
  (cadr (cddddr view)))

(defun avlc-seq (object)
  (avlc-m-seq (avlc-m1 object)))

(defun avlc-hgt (object)
  (avlc-m-hgt (avlc-m1 object)))

;; This is the source fact0, with its case split and balance arithmetic intact.

(defun avlc-fact0-p (view t3)
  (if (avlc-view-empty-p view)
      (and
       (equal (avlc-hgt t3) 0)
       (equal (avlc-seq t3) nil))
    (let* ((left (avlc-view-left view))
           (datum (avlc-view-datum view))
           (right (avlc-view-right view))
           (height (avlc-view-height view))
           (summary (avlc-view-summary view))
           (left-height (avlc-hgt left))
           (right-height (avlc-hgt right))
           (difference (- left-height right-height))
           (bound (avlc-balancing)))
      (and
       (equal
        (avlc-seq t3)
        (avlc-node-model
         (avlc-seq left)
         datum
         (avlc-seq right)))
       (equal
        summary
        (avlc-aggregate-measure
         (avlc-seq t3)))
       (<= (- bound) difference)
       (<= difference bound)
       (equal (avlc-hgt t3) height)
       (equal
        height
        (+ 1
           (if (< left-height right-height)
               right-height
             left-height)))))))

;; The first node branch retains the source universal quantifier over every
;; candidate recursive result o2.

(defun-sk avlc-node-o2-bound-p (left right datum)
  (forall (o2)
    (implies
     (avlc-t2-p o2)
     (implies
      (and
       (equal
        (avlc-seq o2)
        (cons datum (avlc-seq left)))
       (<=
        (- (avlc-hgt o2)
           (avlc-hgt left))
        1)
       (<=
        0
        (- (avlc-hgt o2)
           (avlc-hgt left))))
      (and
       (<=
        (- (- (avlc-balancing)) 1)
        (- (avlc-hgt o2)
           (avlc-hgt right)))
       (<=
        (- (avlc-hgt o2)
           (avlc-hgt right))
        (+ (avlc-balancing) 1)))))))

(defun avlc-first-conclusion-p (view t3 datum)
  (if (avlc-view-empty-p view)
      t
    (let ((left (avlc-view-left view))
          (right (avlc-view-right view)))
      (and
       (<= 0 (avlc-hgt t3))
       (< (avlc-hgt left)
          (avlc-hgt t3))
       (avlc-node-o2-bound-p
        left right datum)))))

;; The existential witness o2 remains internal to the node result premise.

(defun-sk avlc-node-result-premise-p
    (result left node-datum right datum)
  (exists (o2)
    (and
     (avlc-t2-p o2)
     (equal
      (avlc-seq o2)
      (cons datum (avlc-seq left)))
     (<=
      (- (avlc-hgt o2)
         (avlc-hgt left))
      1)
     (<=
      0
      (- (avlc-hgt o2)
         (avlc-hgt left)))
     (equal
      (avlc-seq result)
      (avlc-node-model
       (avlc-seq o2)
       node-datum
       (avlc-seq right)))
     (let* ((left-height (avlc-hgt o2))
            (right-height (avlc-hgt right))
            (expected-height
             (+ 1
                (if (< left-height right-height)
                    right-height
                  left-height)))
            (result-height (avlc-hgt result))
            (height-loss
             (- expected-height result-height))
            (difference
             (- left-height right-height))
            (bound (avlc-balancing)))
       (and
        (<= 0 height-loss)
        (<= height-loss 1)
        (implies
         (and
          (<= (- bound) difference)
          (<= difference bound))
         (equal
          expected-height
          result-height)))))))

(defun avlc-result-premise-p (view result datum)
  (if (avlc-view-empty-p view)
      (and
       (equal
        (avlc-seq result)
        (list datum))
       (equal
        (avlc-hgt result)
        1))
    (avlc-node-result-premise-p
     result
     (avlc-view-left view)
     (avlc-view-datum view)
     (avlc-view-right view)
     datum)))

;; The second top-level conjunct retains the universal result continuation.

(defun-sk avlc-result-continuation-p (view t3 datum)
  (forall (result)
    (implies
     (avlc-t2-p result)
     (implies
      (avlc-result-premise-p
       view result datum)
      (and
       (equal
        (avlc-seq result)
        (cons datum (avlc-seq t3)))
       (<=
        (- (avlc-hgt result)
           (avlc-hgt t3))
        1)
       (<=
        0
        (- (avlc-hgt result)
           (avlc-hgt t3))))))))

(defun-sk ntp4vc-pearl-avl-avl-consqtvc-statement ()
  (forall (o1 t3 d)
    (implies
     (and
      (avlc-view-p o1)
      (avlc-t2-p t3)
      (avlc-t1-p d)
      (avlc-t-p (avlc-zero))
      (avlc-carriers-inhabited-p)
      (natp (avlc-balancing))
      (< 0 (avlc-balancing))
      (avlc-operation-types-p)
      (avlc-associative-p)
      (avlc-neutral-p)
      (avlc-t-invariant-p)
      (avlc-t-injective-p))
     (implies
      (avlc-fact0-p o1 t3)
      (and
       (avlc-first-conclusion-p o1 t3 d)
       (avlc-result-continuation-p
        o1 t3 d))))))

(value-triple :itpeval-statement-checked)
:q
