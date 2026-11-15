;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_back_nodeqtvc: the AVL back-node verification condition
;; relating a node view, stored sequence, tree heights, and the final element.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Unary predicates are conservative interfaces for the three abstract source
;; carriers t, t1 alpha, and t2 alpha at an arbitrary inhabited alpha.

(defstub avl-back-t-p (x) t)
(defstub avl-back-t1-p (x) t)
(defstub avl-back-t2-p (x) t)

(defstub avl-back-zero () t)
(defstub avl-back-op (left right) t)
(defstub avl-back-measure (datum) t)
(defstub avl-back-measure-closure (datum) t)
(defstub avl-back-aggregate (sequence) t)
(defstub avl-back-balancing () t)
(defstub avl-back-repr (object) t)
(defstub avl-back-m1 (object) t)

(defun avl-back-t1-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (avl-back-t1-p (car xs))
     (avl-back-t1-list-p (cdr xs)))))

;; Source trees are represented by NIL for Empty and an exact six-element
;; record (:TREE-NODE left datum right height summary) for Node.

(defun avl-back-tree-empty-p (tree)
  (equal tree nil))

(defun avl-back-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun avl-back-tree-left (tree)
  (cadr tree))

(defun avl-back-tree-datum (tree)
  (caddr tree))

(defun avl-back-tree-right (tree)
  (cadddr tree))

(defun avl-back-tree-height (tree)
  (car (cddddr tree)))

(defun avl-back-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avl-back-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-back-tree-empty-p tree)
      t
    (and
     (avl-back-tree-node-shape-p tree)
     (avl-back-tree-p (avl-back-tree-left tree))
     (avl-back-t1-p (avl-back-tree-datum tree))
     (avl-back-tree-p (avl-back-tree-right tree))
     (natp (avl-back-tree-height tree))
     (avl-back-t-p (avl-back-tree-summary tree)))))

;; The source record m has a t1-list sequence and an integer height.

(defun avl-back-m-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (avl-back-t1-list-p (cadr model))
   (integerp (caddr model))))

(defun avl-back-m-seq (model)
  (cadr model))

(defun avl-back-m-hgt (model)
  (caddr model))

(defun avl-back-node-model (left datum right)
  (append left (cons datum right)))

(defun avl-back-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-back-tree-empty-p tree)
      nil
    (if (avl-back-tree-node-shape-p tree)
        (avl-back-node-model
         (avl-back-seq-model (avl-back-tree-left tree))
         (avl-back-tree-datum tree)
         (avl-back-seq-model (avl-back-tree-right tree)))
      nil)))

(defun avl-back-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-back-tree-empty-p tree)
      0
    (if (avl-back-tree-node-shape-p tree)
        (let ((left-height
               (avl-back-real-height
                (avl-back-tree-left tree)))
              (right-height
               (avl-back-real-height
                (avl-back-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avl-back-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-back-tree-empty-p tree)
      t
    (if (avl-back-tree-node-shape-p tree)
        (let* ((left (avl-back-tree-left tree))
               (right (avl-back-tree-right tree))
               (height (avl-back-tree-height tree))
               (summary (avl-back-tree-summary tree))
               (difference
                (- (avl-back-real-height right)
                   (avl-back-real-height left))))
          (and
           (equal height (avl-back-real-height tree))
           (equal
            summary
            (avl-back-aggregate
             (avl-back-seq-model tree)))
           (<= (- (avl-back-balancing)) difference)
           (<= difference (avl-back-balancing))
           (avl-back-balanced-p left)
           (avl-back-balanced-p right)))
      nil)))

;; Source views use NIL for AEmpty and an exact six-element record
;; (:VIEW-NODE left datum right height summary) for ANode.

(defun avl-back-view-empty-p (view)
  (equal view nil))

(defun avl-back-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun avl-back-view-left (view)
  (cadr view))

(defun avl-back-view-datum (view)
  (caddr view))

(defun avl-back-view-right (view)
  (cadddr view))

(defun avl-back-view-height (view)
  (car (cddddr view)))

(defun avl-back-view-summary (view)
  (cadr (cddddr view)))

(defun avl-back-view-p (view)
  (or
   (avl-back-view-empty-p view)
   (and
    (avl-back-view-node-shape-p view)
    (avl-back-t2-p (avl-back-view-left view))
    (avl-back-t1-p (avl-back-view-datum view))
    (avl-back-t2-p (avl-back-view-right view))
    (natp (avl-back-view-height view))
    (avl-back-t-p (avl-back-view-summary view)))))

;; The following Boolean predicates retain the source theory's carrier
;; nonemptiness, function typing, monoid laws, aggregate laws, positive
;; balancing bound, measure closure, representation invariant, and t2
;; injectivity as explicit assumptions rather than asserted ACL2 events.

(defun-sk avl-back-carriers-inhabited-p ()
  (exists (datum object)
    (and
     (avl-back-t1-p datum)
     (avl-back-t2-p object))))

(defun-sk avl-back-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avl-back-t-p left)
       (avl-back-t-p right))
      (avl-back-t-p
       (avl-back-op left right)))
     (implies
      (avl-back-t1-p datum)
      (and
       (avl-back-t-p
        (avl-back-measure datum))
       (avl-back-t-p
        (avl-back-measure-closure datum))))
     (implies
      (avl-back-t1-list-p sequence)
      (avl-back-t-p
       (avl-back-aggregate sequence)))
     (implies
      (avl-back-t2-p object)
      (and
       (avl-back-tree-p
        (avl-back-repr object))
       (avl-back-m-p
        (avl-back-m1 object)))))))

(defun-sk avl-back-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avl-back-t-p a)
      (avl-back-t-p b)
      (avl-back-t-p c))
     (equal
      (avl-back-op a (avl-back-op b c))
      (avl-back-op (avl-back-op a b) c)))))

(defun-sk avl-back-neutral-p ()
  (forall (x)
    (implies
     (avl-back-t-p x)
     (and
      (equal
       (avl-back-op x (avl-back-zero))
       x)
      (equal
       x
       (avl-back-op (avl-back-zero) x))))))

(defun-sk avl-back-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avl-back-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avl-back-aggregate sequence)
      (avl-back-measure-closure
       (car sequence))))))

(defun-sk avl-back-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avl-back-t1-list-p left)
      (avl-back-t1-list-p right))
     (equal
      (avl-back-aggregate
       (append left right))
      (avl-back-op
       (avl-back-aggregate left)
       (avl-back-aggregate right))))))

(defun-sk avl-back-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avl-back-t1-p datum)
     (equal
      (avl-back-measure-closure datum)
      (avl-back-measure datum)))))

(defun-sk avl-back-invariant-p ()
  (forall (object)
    (implies
     (avl-back-t2-p object)
     (let ((tree (avl-back-repr object))
           (model (avl-back-m1 object)))
       (and
        (avl-back-balanced-p tree)
        (equal
         (avl-back-m-seq model)
         (avl-back-seq-model tree))
        (equal
         (avl-back-m-hgt model)
         (avl-back-real-height tree)))))))

(defun-sk avl-back-t2-injective-p ()
  (forall (left right)
    (implies
     (and
      (avl-back-t2-p left)
      (avl-back-t2-p right)
      (equal
       (avl-back-repr left)
       (avl-back-repr right))
      (equal
       (avl-back-m1 left)
       (avl-back-m1 right)))
     (equal left right))))

(defun avl-back-background-p ()
  (and
   (avl-back-t-p (avl-back-zero))
   (natp (avl-back-balancing))
   (< 0 (avl-back-balancing))
   (avl-back-carriers-inhabited-p)
   (avl-back-function-closures-p)
   (avl-back-associative-p)
   (avl-back-neutral-p)
   (equal
    (avl-back-aggregate nil)
    (avl-back-zero))
   (avl-back-aggregate-singleton-law-p)
   (avl-back-aggregate-concatenation-law-p)
   (avl-back-measure-closure-law-p)
   (avl-back-invariant-p)
   (avl-back-t2-injective-p)))

(defun avl-back-sequence (object)
  (avl-back-m-seq
   (avl-back-m1 object)))

(defun avl-back-height (object)
  (avl-back-m-hgt
   (avl-back-m1 object)))

(defun avl-back-fact0-p (view object)
  (if (avl-back-view-empty-p view)
      (and
       (equal (avl-back-height object) 0)
       (equal (avl-back-sequence object) nil))
    (let* ((left (avl-back-view-left view))
           (right (avl-back-view-right view))
           (datum (avl-back-view-datum view))
           (height (avl-back-view-height view))
           (summary (avl-back-view-summary view))
           (left-height (avl-back-height left))
           (right-height (avl-back-height right))
           (difference (- left-height right-height)))
      (and
       (equal
        (avl-back-sequence object)
        (avl-back-node-model
         (avl-back-sequence left)
         datum
         (avl-back-sequence right)))
       (equal
        summary
        (avl-back-aggregate
         (avl-back-sequence object)))
       (<= (- (avl-back-balancing)) difference)
       (<= difference (avl-back-balancing))
       (equal
        (avl-back-height object)
        height)
       (equal
        height
        (+ 1
           (if (< left-height right-height)
               right-height
             left-height)))))))

(defun avl-back-height-conclusion-p (view object)
  (if (avl-back-view-empty-p view)
      t
    (and
     (<= 0 (avl-back-height object))
     (<
      (avl-back-height
       (avl-back-view-right view))
      (avl-back-height object)))))

(defun-sk avl-back-result-conclusion-p (view object datum)
  (forall (result)
    (implies
     (avl-back-t1-p result)
     (implies
      (if (avl-back-view-empty-p view)
          (equal result datum)
        (let ((right
               (avl-back-view-right view))
              (node-datum
               (avl-back-view-datum view)))
          (equal
           result
           (nth
            (len (avl-back-sequence right))
            (cons
             node-datum
             (avl-back-sequence right))))))
      (equal
       result
       (nth
        (len (avl-back-sequence object))
        (cons
         datum
         (avl-back-sequence object))))))))

(defun-sk ntp4vc-pearl-avl-avl-back-nodeqtvc-statement ()
  (forall (view object datum)
    (implies
     (and
      (avl-back-background-p)
      (avl-back-view-p view)
      (avl-back-t2-p object)
      (avl-back-t1-p datum)
      (avl-back-fact0-p view object))
     (and
      (avl-back-height-conclusion-p view object)
      (avl-back-result-conclusion-p
       view object datum)))))

(value-triple :itpeval-statement-checked)
:q
