;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_front_nodeqtvc: the AVL front-node verification condition
;; relating a node view, stored sequence, tree heights, and the initial element.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Unary predicates are conservative interfaces for the three abstract source
;; carriers t, t1 alpha, and t2 alpha at an arbitrary inhabited alpha.

(defstub avl-front-t-p (x) t)
(defstub avl-front-t1-p (x) t)
(defstub avl-front-t2-p (x) t)

(defstub avl-front-zero () t)
(defstub avl-front-op (left right) t)
(defstub avl-front-measure (datum) t)
(defstub avl-front-measure-closure (datum) t)
(defstub avl-front-aggregate (sequence) t)
(defstub avl-front-balancing () t)
(defstub avl-front-repr (object) t)
(defstub avl-front-m1 (object) t)

(defun avl-front-t1-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (avl-front-t1-p (car xs))
     (avl-front-t1-list-p (cdr xs)))))

;; Source trees are represented by NIL for Empty and an exact six-element
;; record (:TREE-NODE left datum right height summary) for Node.

(defun avl-front-tree-empty-p (tree)
  (equal tree nil))

(defun avl-front-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun avl-front-tree-left (tree)
  (cadr tree))

(defun avl-front-tree-datum (tree)
  (caddr tree))

(defun avl-front-tree-right (tree)
  (cadddr tree))

(defun avl-front-tree-height (tree)
  (car (cddddr tree)))

(defun avl-front-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avl-front-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-front-tree-empty-p tree)
      t
    (and
     (avl-front-tree-node-shape-p tree)
     (avl-front-tree-p (avl-front-tree-left tree))
     (avl-front-t1-p (avl-front-tree-datum tree))
     (avl-front-tree-p (avl-front-tree-right tree))
     (natp (avl-front-tree-height tree))
     (avl-front-t-p (avl-front-tree-summary tree)))))

;; The source record m has a t1-list sequence and an integer height.

(defun avl-front-m-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (avl-front-t1-list-p (cadr model))
   (integerp (caddr model))))

(defun avl-front-m-seq (model)
  (cadr model))

(defun avl-front-m-hgt (model)
  (caddr model))

(defun avl-front-node-model (left datum right)
  (append left (cons datum right)))

(defun avl-front-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-front-tree-empty-p tree)
      nil
    (if (avl-front-tree-node-shape-p tree)
        (avl-front-node-model
         (avl-front-seq-model (avl-front-tree-left tree))
         (avl-front-tree-datum tree)
         (avl-front-seq-model (avl-front-tree-right tree)))
      nil)))

(defun avl-front-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-front-tree-empty-p tree)
      0
    (if (avl-front-tree-node-shape-p tree)
        (let ((left-height
               (avl-front-real-height
                (avl-front-tree-left tree)))
              (right-height
               (avl-front-real-height
                (avl-front-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avl-front-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-front-tree-empty-p tree)
      t
    (if (avl-front-tree-node-shape-p tree)
        (let* ((left (avl-front-tree-left tree))
               (right (avl-front-tree-right tree))
               (height (avl-front-tree-height tree))
               (summary (avl-front-tree-summary tree))
               (difference
                (- (avl-front-real-height right)
                   (avl-front-real-height left))))
          (and
           (equal height (avl-front-real-height tree))
           (equal
            summary
            (avl-front-aggregate
             (avl-front-seq-model tree)))
           (<= (- (avl-front-balancing)) difference)
           (<= difference (avl-front-balancing))
           (avl-front-balanced-p left)
           (avl-front-balanced-p right)))
      nil)))

;; Source views use NIL for AEmpty and an exact six-element record
;; (:VIEW-NODE left datum right height summary) for ANode.

(defun avl-front-view-empty-p (view)
  (equal view nil))

(defun avl-front-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun avl-front-view-left (view)
  (cadr view))

(defun avl-front-view-datum (view)
  (caddr view))

(defun avl-front-view-right (view)
  (cadddr view))

(defun avl-front-view-height (view)
  (car (cddddr view)))

(defun avl-front-view-summary (view)
  (cadr (cddddr view)))

(defun avl-front-view-p (view)
  (or
   (avl-front-view-empty-p view)
   (and
    (avl-front-view-node-shape-p view)
    (avl-front-t2-p (avl-front-view-left view))
    (avl-front-t1-p (avl-front-view-datum view))
    (avl-front-t2-p (avl-front-view-right view))
    (natp (avl-front-view-height view))
    (avl-front-t-p (avl-front-view-summary view)))))

;; The following Boolean predicates retain the source theory's carrier
;; nonemptiness, function typing, monoid laws, aggregate laws, positive
;; balancing bound, measure closure, representation invariant, and t2
;; injectivity as explicit assumptions rather than asserted ACL2 events.

(defun-sk avl-front-carriers-inhabited-p ()
  (exists (datum object)
    (and
     (avl-front-t1-p datum)
     (avl-front-t2-p object))))

(defun-sk avl-front-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avl-front-t-p left)
       (avl-front-t-p right))
      (avl-front-t-p
       (avl-front-op left right)))
     (implies
      (avl-front-t1-p datum)
      (and
       (avl-front-t-p
        (avl-front-measure datum))
       (avl-front-t-p
        (avl-front-measure-closure datum))))
     (implies
      (avl-front-t1-list-p sequence)
      (avl-front-t-p
       (avl-front-aggregate sequence)))
     (implies
      (avl-front-t2-p object)
      (and
       (avl-front-tree-p
        (avl-front-repr object))
       (avl-front-m-p
        (avl-front-m1 object)))))))

(defun-sk avl-front-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avl-front-t-p a)
      (avl-front-t-p b)
      (avl-front-t-p c))
     (equal
      (avl-front-op a (avl-front-op b c))
      (avl-front-op (avl-front-op a b) c)))))

(defun-sk avl-front-neutral-p ()
  (forall (x)
    (implies
     (avl-front-t-p x)
     (and
      (equal
       (avl-front-op x (avl-front-zero))
       x)
      (equal
       x
       (avl-front-op (avl-front-zero) x))))))

(defun-sk avl-front-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avl-front-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avl-front-aggregate sequence)
      (avl-front-measure-closure
       (car sequence))))))

(defun-sk avl-front-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avl-front-t1-list-p left)
      (avl-front-t1-list-p right))
     (equal
      (avl-front-aggregate
       (append left right))
      (avl-front-op
       (avl-front-aggregate left)
       (avl-front-aggregate right))))))

(defun-sk avl-front-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avl-front-t1-p datum)
     (equal
      (avl-front-measure-closure datum)
      (avl-front-measure datum)))))

(defun-sk avl-front-invariant-p ()
  (forall (object)
    (implies
     (avl-front-t2-p object)
     (let ((tree (avl-front-repr object))
           (model (avl-front-m1 object)))
       (and
        (avl-front-balanced-p tree)
        (equal
         (avl-front-m-seq model)
         (avl-front-seq-model tree))
        (equal
         (avl-front-m-hgt model)
         (avl-front-real-height tree)))))))

(defun-sk avl-front-t2-injective-p ()
  (forall (left right)
    (implies
     (and
      (avl-front-t2-p left)
      (avl-front-t2-p right)
      (equal
       (avl-front-repr left)
       (avl-front-repr right))
      (equal
       (avl-front-m1 left)
       (avl-front-m1 right)))
     (equal left right))))

(defun avl-front-background-p ()
  (and
   (avl-front-t-p (avl-front-zero))
   (natp (avl-front-balancing))
   (< 0 (avl-front-balancing))
   (avl-front-carriers-inhabited-p)
   (avl-front-function-closures-p)
   (avl-front-associative-p)
   (avl-front-neutral-p)
   (equal
    (avl-front-aggregate nil)
    (avl-front-zero))
   (avl-front-aggregate-singleton-law-p)
   (avl-front-aggregate-concatenation-law-p)
   (avl-front-measure-closure-law-p)
   (avl-front-invariant-p)
   (avl-front-t2-injective-p)))

(defun avl-front-sequence (object)
  (avl-front-m-seq
   (avl-front-m1 object)))

(defun avl-front-height (object)
  (avl-front-m-hgt
   (avl-front-m1 object)))

(defun avl-front-fact0-p (view object)
  (if (avl-front-view-empty-p view)
      (and
       (equal (avl-front-height object) 0)
       (equal (avl-front-sequence object) nil))
    (let* ((left (avl-front-view-left view))
           (right (avl-front-view-right view))
           (datum (avl-front-view-datum view))
           (height (avl-front-view-height view))
           (summary (avl-front-view-summary view))
           (left-height (avl-front-height left))
           (right-height (avl-front-height right))
           (difference (- left-height right-height)))
      (and
       (equal
        (avl-front-sequence object)
        (avl-front-node-model
         (avl-front-sequence left)
         datum
         (avl-front-sequence right)))
       (equal
        summary
        (avl-front-aggregate
         (avl-front-sequence object)))
       (<= (- (avl-front-balancing)) difference)
       (<= difference (avl-front-balancing))
       (equal
        (avl-front-height object)
        height)
       (equal
        height
        (+ 1
           (if (< left-height right-height)
               right-height
             left-height)))))))

(defun avl-front-height-conclusion-p (view object)
  (if (avl-front-view-empty-p view)
      t
    (and
     (<= 0 (avl-front-height object))
     (<
      (avl-front-height
       (avl-front-view-left view))
      (avl-front-height object)))))

(defun-sk avl-front-result-conclusion-p (view object datum)
  (forall (result)
    (implies
     (avl-front-t1-p result)
     (implies
      (if (avl-front-view-empty-p view)
          (equal result datum)
        (let ((left
               (avl-front-view-left view))
              (node-datum
               (avl-front-view-datum view)))
          (equal
           result
           (nth
            0
            (append
             (avl-front-sequence left)
             (list node-datum))))))
      (equal
       result
       (nth
        0
        (append
         (avl-front-sequence object)
         (list datum))))))))

(defun-sk ntp4vc-pearl-avl-avl-front-nodeqtvc-statement ()
  (forall (view object datum)
    (implies
     (and
      (avl-front-background-p)
      (avl-front-view-p view)
      (avl-front-t2-p object)
      (avl-front-t1-p datum)
      (avl-front-fact0-p view object))
     (and
      (avl-front-height-conclusion-p view object)
      (avl-front-result-conclusion-p
       view object datum)))))

(value-triple :itpeval-statement-checked)
:q
