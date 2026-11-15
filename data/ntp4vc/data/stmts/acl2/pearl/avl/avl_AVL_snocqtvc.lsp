;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_snocqtvc: the AVL snoc verification condition relating
;; sequence append, stored heights, balance bounds, and recursive results.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the arbitrary source carriers t, t1 alpha,
;; and t2 alpha at a fixed arbitrary inhabited alpha.

(defstub avls-t-recognizer (x) t)
(defstub avls-t1-recognizer (x) t)
(defstub avls-t2-recognizer (x) t)
(defstub avls-zero () t)
(defstub avls-op (left right) t)
(defstub avls-measure (datum) t)
(defstub avls-measure-closure (datum) t)
(defstub avls-aggregate (sequence) t)
(defstub avls-balancing () t)
(defstub avls-repr (object) t)
(defstub avls-m1 (object) t)

(defun avls-t-p (x)
  (if (avls-t-recognizer x) t nil))

(defun avls-t1-p (x)
  (if (avls-t1-recognizer x) t nil))

(defun avls-t2-p (x)
  (if (avls-t2-recognizer x) t nil))

(defun avls-t1-list-p (xs)
  (if (consp xs)
      (and
       (avls-t1-p (car xs))
       (avls-t1-list-p (cdr xs)))
    (equal xs nil)))

;; The source model record m contains a sequence and an integer height.

(defun avls-m (sequence height)
  (list :avls-m sequence height))

(defun avls-m-p (object)
  (and
   (true-listp object)
   (equal (len object) 3)
   (equal (car object) :avls-m)
   (avls-t1-list-p (cadr object))
   (integerp (caddr object))))

(defun avls-m-seq (object)
  (cadr object))

(defun avls-m-hgt (object)
  (caddr object))

;; Tagged finite trees faithfully represent the source inductive tree.

(defun avls-empty ()
  (list :avls-empty))

(defun avls-node (left datum right height summary)
  (list :avls-node left datum right height summary))

(defun avls-tree-empty-p (tree)
  (equal tree (avls-empty)))

(defun avls-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :avls-node)))

(defun avls-tree-left (tree)
  (cadr tree))

(defun avls-tree-datum (tree)
  (caddr tree))

(defun avls-tree-right (tree)
  (cadddr tree))

(defun avls-tree-height (tree)
  (car (cddddr tree)))

(defun avls-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avls-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avls-tree-empty-p tree)
      t
    (and
     (avls-tree-node-shape-p tree)
     (avls-tree-p (avls-tree-left tree))
     (avls-t1-p (avls-tree-datum tree))
     (avls-tree-p (avls-tree-right tree))
     (natp (avls-tree-height tree))
     (avls-t-p (avls-tree-summary tree)))))

(defun avls-node-model (left datum right)
  (append left (cons datum right)))

(defun avls-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avls-tree-empty-p tree)
      nil
    (if (avls-tree-node-shape-p tree)
        (avls-node-model
         (avls-seq-model (avls-tree-left tree))
         (avls-tree-datum tree)
         (avls-seq-model (avls-tree-right tree)))
      nil)))

(defun avls-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avls-tree-empty-p tree)
      0
    (if (avls-tree-node-shape-p tree)
        (let ((left-height
               (avls-real-height (avls-tree-left tree)))
              (right-height
               (avls-real-height (avls-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avls-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avls-tree-empty-p tree)
      t
    (if (avls-tree-node-shape-p tree)
        (let* ((left (avls-tree-left tree))
               (right (avls-tree-right tree))
               (difference
                (- (avls-real-height right)
                   (avls-real-height left)))
               (bound (avls-balancing)))
          (and
           (equal
            (avls-tree-height tree)
            (avls-real-height tree))
           (equal
            (avls-tree-summary tree)
            (avls-aggregate
             (avls-seq-model tree)))
           (<= (- bound) difference)
           (<= difference bound)
           (avls-balanced-p left)
           (avls-balanced-p right)))
      nil)))

;; Source carrier nonemptiness, function typing, monoid laws, aggregate laws,
;; representation invariants, and injectivity remain explicit assumptions.

(defun-sk avls-carriers-inhabited-p ()
  (exists (datum object)
    (and
     (avls-t1-p datum)
     (avls-t2-p object))))

(defun-sk avls-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avls-t-p left)
       (avls-t-p right))
      (avls-t-p
       (avls-op left right)))
     (implies
      (avls-t1-p datum)
      (and
       (avls-t-p
        (avls-measure datum))
       (avls-t-p
        (avls-measure-closure datum))))
     (implies
      (avls-t1-list-p sequence)
      (avls-t-p
       (avls-aggregate sequence)))
     (implies
      (avls-t2-p object)
      (and
       (avls-tree-p
        (avls-repr object))
       (avls-m-p
        (avls-m1 object)))))))

(defun-sk avls-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avls-t-p a)
      (avls-t-p b)
      (avls-t-p c))
     (equal
      (avls-op a (avls-op b c))
      (avls-op (avls-op a b) c)))))

(defun-sk avls-neutral-p ()
  (forall (x)
    (implies
     (avls-t-p x)
     (and
      (equal
       (avls-op x (avls-zero))
       x)
      (equal
       x
       (avls-op (avls-zero) x))))))

(defun-sk avls-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avls-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avls-aggregate sequence)
      (avls-measure-closure
       (car sequence))))))

(defun-sk avls-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avls-t1-list-p left)
      (avls-t1-list-p right))
     (equal
      (avls-aggregate
       (append left right))
      (avls-op
       (avls-aggregate left)
       (avls-aggregate right))))))

(defun-sk avls-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avls-t1-p datum)
     (equal
      (avls-measure-closure datum)
      (avls-measure datum)))))

(defun-sk avls-t-invariant-p ()
  (forall (self)
    (implies
     (avls-t2-p self)
     (and
      (avls-balanced-p
       (avls-repr self))
      (equal
       (avls-m-seq (avls-m1 self))
       (avls-seq-model (avls-repr self)))
      (equal
       (avls-m-hgt (avls-m1 self))
       (avls-real-height
        (avls-repr self)))))))

(defun-sk avls-t-injective-p ()
  (forall (left right)
    (implies
     (and
      (avls-t2-p left)
      (avls-t2-p right)
      (equal
       (avls-repr left)
       (avls-repr right))
      (equal
       (avls-m1 left)
       (avls-m1 right)))
     (equal left right))))

(defun avls-background-p ()
  (and
   (avls-t-p (avls-zero))
   (natp (avls-balancing))
   (< 0 (avls-balancing))
   (avls-carriers-inhabited-p)
   (avls-function-closures-p)
   (avls-associative-p)
   (avls-neutral-p)
   (equal
    (avls-aggregate nil)
    (avls-zero))
   (avls-aggregate-singleton-law-p)
   (avls-aggregate-concatenation-law-p)
   (avls-measure-closure-law-p)
   (avls-t-invariant-p)
   (avls-t-injective-p)))

;; Tagged values retain the source view datatype and all field types.

(defun avls-aempty ()
  (list :avls-aempty))

(defun avls-anode (left datum right height summary)
  (list :avls-anode left datum right height summary))

(defun avls-view-empty-p (view)
  (equal view (avls-aempty)))

(defun avls-view-node-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :avls-anode)
   (avls-t2-p (cadr view))
   (avls-t1-p (caddr view))
   (avls-t2-p (cadddr view))
   (natp (car (cddddr view)))
   (avls-t-p (cadr (cddddr view)))))

(defun avls-view-p (view)
  (or
   (avls-view-empty-p view)
   (avls-view-node-p view)))

(defun avls-view-left (view)
  (cadr view))

(defun avls-view-datum (view)
  (caddr view))

(defun avls-view-right (view)
  (cadddr view))

(defun avls-view-height (view)
  (car (cddddr view)))

(defun avls-view-summary (view)
  (cadr (cddddr view)))

(defun avls-seq (object)
  (avls-m-seq (avls-m1 object)))

(defun avls-hgt (object)
  (avls-m-hgt (avls-m1 object)))

;; This is fact0, including its complete view case split and height equation.

(defun avls-fact0-p (view t3)
  (if (avls-view-empty-p view)
      (and
       (equal (avls-hgt t3) 0)
       (equal (avls-seq t3) nil))
    (let* ((left (avls-view-left view))
           (datum (avls-view-datum view))
           (right (avls-view-right view))
           (height (avls-view-height view))
           (summary (avls-view-summary view))
           (left-height (avls-hgt left))
           (right-height (avls-hgt right))
           (difference (- left-height right-height))
           (bound (avls-balancing)))
      (and
       (equal
        (avls-seq t3)
        (avls-node-model
         (avls-seq left)
         datum
         (avls-seq right)))
       (equal
        summary
        (avls-aggregate
         (avls-seq t3)))
       (<= (- bound) difference)
       (<= difference bound)
       (equal (avls-hgt t3) height)
       (equal
        height
        (+ 1
           (if (< left-height right-height)
               right-height
             left-height)))))))

;; The first node branch retains the universal quantifier over every
;; candidate recursive result o2.

(defun-sk avls-node-o2-bound-p (left right datum)
  (forall (o2)
    (implies
     (avls-t2-p o2)
     (implies
      (and
       (equal
        (avls-seq o2)
        (append
         (avls-seq right)
         (list datum)))
       (<=
        (- (avls-hgt o2)
           (avls-hgt right))
        1)
       (<=
        0
        (- (avls-hgt o2)
           (avls-hgt right))))
      (and
       (<=
        (- (- (avls-balancing)) 1)
        (- (avls-hgt left)
           (avls-hgt o2)))
       (<=
        (- (avls-hgt left)
           (avls-hgt o2))
        (+ (avls-balancing) 1)))))))

(defun avls-first-conclusion-p (view t3 datum)
  (if (avls-view-empty-p view)
      t
    (let ((left (avls-view-left view))
          (right (avls-view-right view)))
      (and
       (<= 0 (avls-hgt t3))
       (< (avls-hgt right)
          (avls-hgt t3))
       (avls-node-o2-bound-p
        left right datum)))))

;; The existential witness o2 remains internal to the node result premise.

(defun-sk avls-node-result-premise-p
    (result left node-datum right datum)
  (exists (o2)
    (and
     (avls-t2-p o2)
     (equal
      (avls-seq o2)
      (append
       (avls-seq right)
       (list datum)))
     (<=
      (- (avls-hgt o2)
         (avls-hgt right))
      1)
     (<=
      0
      (- (avls-hgt o2)
         (avls-hgt right)))
     (equal
      (avls-seq result)
      (avls-node-model
       (avls-seq left)
       node-datum
       (avls-seq o2)))
     (let* ((left-height (avls-hgt left))
            (right-height (avls-hgt o2))
            (expected-height
             (+ 1
                (if (< left-height right-height)
                    right-height
                  left-height)))
            (result-height (avls-hgt result))
            (height-loss
             (- expected-height result-height))
            (difference
             (- left-height right-height))
            (bound (avls-balancing)))
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

(defun avls-result-premise-p (view result datum)
  (if (avls-view-empty-p view)
      (and
       (equal
        (avls-seq result)
        (list datum))
       (equal
        (avls-hgt result)
        1))
    (avls-node-result-premise-p
     result
     (avls-view-left view)
     (avls-view-datum view)
     (avls-view-right view)
     datum)))

;; The second top-level conjunct retains the universal result continuation.

(defun-sk avls-result-continuation-p (view t3 datum)
  (forall (result)
    (implies
     (avls-t2-p result)
     (implies
      (avls-result-premise-p
       view result datum)
      (and
       (equal
        (avls-seq result)
        (append
         (avls-seq t3)
         (list datum)))
       (<=
        (- (avls-hgt result)
           (avls-hgt t3))
        1)
       (<=
        0
        (- (avls-hgt result)
           (avls-hgt t3))))))))

(defun-sk ntp4vc-pearl-avl-avl-snocqtvc-statement ()
  (forall (o1 t3 d)
    (implies
     (and
      (avls-view-p o1)
      (avls-t2-p t3)
      (avls-t1-p d)
      (avls-background-p))
     (implies
      (avls-fact0-p o1 t3)
      (and
       (avls-first-conclusion-p o1 t3 d)
       (avls-result-continuation-p
        o1 t3 d))))))

(value-triple :itpeval-statement-checked)
:q
