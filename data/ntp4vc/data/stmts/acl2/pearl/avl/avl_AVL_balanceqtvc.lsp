;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_balanceqtvc: the AVL balance verification condition
;; for sequence preservation and bounded height change across rotations.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces for the abstract carriers t, t1 alpha, and
;; t2 alpha at an arbitrary inhabited alpha.

(defstub avl-bal-t-p (x) t)
(defstub avl-bal-t1-p (x) t)
(defstub avl-bal-t2-p (x) t)

(defstub avl-bal-zero () t)
(defstub avl-bal-op (left right) t)
(defstub avl-bal-measure (datum) t)
(defstub avl-bal-measure-closure (datum) t)
(defstub avl-bal-aggregate (sequence) t)
(defstub avl-bal-balancing () t)
(defstub avl-bal-repr (object) t)
(defstub avl-bal-m1 (object) t)

(defun avl-bal-t1-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (avl-bal-t1-p (car xs))
     (avl-bal-t1-list-p (cdr xs)))))

;; Empty trees are NIL.  Nodes are exact records
;; (:TREE-NODE left datum right height summary).

(defun avl-bal-tree-empty-p (tree)
  (equal tree nil))

(defun avl-bal-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun avl-bal-tree-left (tree)
  (cadr tree))

(defun avl-bal-tree-datum (tree)
  (caddr tree))

(defun avl-bal-tree-right (tree)
  (cadddr tree))

(defun avl-bal-tree-height (tree)
  (car (cddddr tree)))

(defun avl-bal-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avl-bal-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-bal-tree-empty-p tree)
      t
    (and
     (avl-bal-tree-node-shape-p tree)
     (avl-bal-tree-p (avl-bal-tree-left tree))
     (avl-bal-t1-p (avl-bal-tree-datum tree))
     (avl-bal-tree-p (avl-bal-tree-right tree))
     (natp (avl-bal-tree-height tree))
     (avl-bal-t-p (avl-bal-tree-summary tree)))))

;; The model record m is (:M sequence height).

(defun avl-bal-m-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (avl-bal-t1-list-p (cadr model))
   (integerp (caddr model))))

(defun avl-bal-m-seq (model)
  (cadr model))

(defun avl-bal-m-hgt (model)
  (caddr model))

(defun avl-bal-node-model (left datum right)
  (append left (cons datum right)))

(defun avl-bal-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-bal-tree-empty-p tree)
      nil
    (if (avl-bal-tree-node-shape-p tree)
        (avl-bal-node-model
         (avl-bal-seq-model (avl-bal-tree-left tree))
         (avl-bal-tree-datum tree)
         (avl-bal-seq-model (avl-bal-tree-right tree)))
      nil)))

(defun avl-bal-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-bal-tree-empty-p tree)
      0
    (if (avl-bal-tree-node-shape-p tree)
        (let ((left-height
               (avl-bal-real-height
                (avl-bal-tree-left tree)))
              (right-height
               (avl-bal-real-height
                (avl-bal-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avl-bal-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avl-bal-tree-empty-p tree)
      t
    (if (avl-bal-tree-node-shape-p tree)
        (let* ((left (avl-bal-tree-left tree))
               (right (avl-bal-tree-right tree))
               (height (avl-bal-tree-height tree))
               (summary (avl-bal-tree-summary tree))
               (difference
                (- (avl-bal-real-height right)
                   (avl-bal-real-height left))))
          (and
           (equal height (avl-bal-real-height tree))
           (equal
            summary
            (avl-bal-aggregate
             (avl-bal-seq-model tree)))
           (<= (- (avl-bal-balancing)) difference)
           (<= difference (avl-bal-balancing))
           (avl-bal-balanced-p left)
           (avl-bal-balanced-p right)))
      nil)))

;; Empty views are NIL.  Nodes are exact records
;; (:VIEW-NODE left datum right height summary).

(defun avl-bal-view-empty-p (view)
  (equal view nil))

(defun avl-bal-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun avl-bal-view-left (view)
  (cadr view))

(defun avl-bal-view-datum (view)
  (caddr view))

(defun avl-bal-view-right (view)
  (cadddr view))

(defun avl-bal-view-height (view)
  (car (cddddr view)))

(defun avl-bal-view-summary (view)
  (cadr (cddddr view)))

(defun avl-bal-view-p (view)
  (or
   (avl-bal-view-empty-p view)
   (and
    (avl-bal-view-node-shape-p view)
    (avl-bal-t2-p (avl-bal-view-left view))
    (avl-bal-t1-p (avl-bal-view-datum view))
    (avl-bal-t2-p (avl-bal-view-right view))
    (natp (avl-bal-view-height view))
    (avl-bal-t-p (avl-bal-view-summary view)))))

;; The source theory's carrier, closure, algebra, aggregate, positivity,
;; representation-invariant, and injectivity assumptions remain explicit
;; Boolean hypotheses of the statement.

(defun-sk avl-bal-carriers-inhabited-p ()
  (exists (datum object)
    (and
     (avl-bal-t1-p datum)
     (avl-bal-t2-p object))))

(defun-sk avl-bal-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avl-bal-t-p left)
       (avl-bal-t-p right))
      (avl-bal-t-p
       (avl-bal-op left right)))
     (implies
      (avl-bal-t1-p datum)
      (and
       (avl-bal-t-p
        (avl-bal-measure datum))
       (avl-bal-t-p
        (avl-bal-measure-closure datum))))
     (implies
      (avl-bal-t1-list-p sequence)
      (avl-bal-t-p
       (avl-bal-aggregate sequence)))
     (implies
      (avl-bal-t2-p object)
      (and
       (avl-bal-tree-p
        (avl-bal-repr object))
       (avl-bal-m-p
        (avl-bal-m1 object)))))))

(defun-sk avl-bal-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avl-bal-t-p a)
      (avl-bal-t-p b)
      (avl-bal-t-p c))
     (equal
      (avl-bal-op a (avl-bal-op b c))
      (avl-bal-op (avl-bal-op a b) c)))))

(defun-sk avl-bal-neutral-p ()
  (forall (x)
    (implies
     (avl-bal-t-p x)
     (and
      (equal
       (avl-bal-op x (avl-bal-zero))
       x)
      (equal
       x
       (avl-bal-op (avl-bal-zero) x))))))

(defun-sk avl-bal-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avl-bal-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avl-bal-aggregate sequence)
      (avl-bal-measure-closure
       (car sequence))))))

(defun-sk avl-bal-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avl-bal-t1-list-p left)
      (avl-bal-t1-list-p right))
     (equal
      (avl-bal-aggregate
       (append left right))
      (avl-bal-op
       (avl-bal-aggregate left)
       (avl-bal-aggregate right))))))

(defun-sk avl-bal-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avl-bal-t1-p datum)
     (equal
      (avl-bal-measure-closure datum)
      (avl-bal-measure datum)))))

(defun-sk avl-bal-invariant-p ()
  (forall (object)
    (implies
     (avl-bal-t2-p object)
     (let ((tree (avl-bal-repr object))
           (model (avl-bal-m1 object)))
       (and
        (avl-bal-balanced-p tree)
        (equal
         (avl-bal-m-seq model)
         (avl-bal-seq-model tree))
        (equal
         (avl-bal-m-hgt model)
         (avl-bal-real-height tree)))))))

(defun-sk avl-bal-t2-injective-p ()
  (forall (left right)
    (implies
     (and
      (avl-bal-t2-p left)
      (avl-bal-t2-p right)
      (equal
       (avl-bal-repr left)
       (avl-bal-repr right))
      (equal
       (avl-bal-m1 left)
       (avl-bal-m1 right)))
     (equal left right))))

(defun avl-bal-background-p ()
  (and
   (avl-bal-t-p (avl-bal-zero))
   (natp (avl-bal-balancing))
   (< 0 (avl-bal-balancing))
   (avl-bal-carriers-inhabited-p)
   (avl-bal-function-closures-p)
   (avl-bal-associative-p)
   (avl-bal-neutral-p)
   (equal
    (avl-bal-aggregate nil)
    (avl-bal-zero))
   (avl-bal-aggregate-singleton-law-p)
   (avl-bal-aggregate-concatenation-law-p)
   (avl-bal-measure-closure-law-p)
   (avl-bal-invariant-p)
   (avl-bal-t2-injective-p)))

(defun avl-bal-sequence (object)
  (avl-bal-m-seq
   (avl-bal-m1 object)))

(defun avl-bal-height (object)
  (avl-bal-m-hgt
   (avl-bal-m1 object)))

(defun avl-bal-max (left right)
  (if (< left right)
      right
    left))

(defun avl-bal-within-p (left-height right-height)
  (let ((difference (- left-height right-height)))
    (and
     (<= (- (avl-bal-balancing)) difference)
     (<= difference (avl-bal-balancing)))))

(defun avl-bal-built-p (object left datum right)
  (and
   (equal
    (avl-bal-sequence object)
    (avl-bal-node-model
     (avl-bal-sequence left)
     datum
     (avl-bal-sequence right)))
   (equal
    (avl-bal-height object)
    (+ 1
       (avl-bal-max
        (avl-bal-height left)
        (avl-bal-height right))))))

(defun avl-bal-view-describes-p (view object)
  (if (avl-bal-view-empty-p view)
      (and
       (equal (avl-bal-height object) 0)
       (equal (avl-bal-sequence object) nil))
    (let* ((left (avl-bal-view-left view))
           (right (avl-bal-view-right view))
           (datum (avl-bal-view-datum view))
           (height (avl-bal-view-height view))
           (summary (avl-bal-view-summary view))
           (left-height (avl-bal-height left))
           (right-height (avl-bal-height right)))
      (and
       (equal
        (avl-bal-sequence object)
        (avl-bal-node-model
         (avl-bal-sequence left)
         datum
         (avl-bal-sequence right)))
       (equal
        summary
        (avl-bal-aggregate
         (avl-bal-sequence object)))
       (avl-bal-within-p left-height right-height)
       (equal (avl-bal-height object) height)
       (equal
        height
        (+ 1
           (avl-bal-max left-height right-height)))))))

;; Universal obligations for the left-heavy single-rotation branch.

(defun-sk avl-bal-left-single-universal-p (ll lr r d)
  (forall (o5)
    (implies
     (avl-bal-t2-p o5)
     (implies
      (avl-bal-built-p o5 lr d r)
      (avl-bal-within-p
       (avl-bal-height ll)
       (avl-bal-height o5))))))

;; Universal obligations for the left-heavy double-rotation branch.

(defun-sk avl-bal-left-double-outer-universal-p
  (ll ld lrl o6)
  (forall (o7)
    (implies
     (avl-bal-t2-p o7)
     (implies
      (avl-bal-built-p o7 ll ld lrl)
      (avl-bal-within-p
       (avl-bal-height o7)
       (avl-bal-height o6))))))

(defun-sk avl-bal-left-double-inner-universal-p
  (ll ld lrl lrr r d)
  (forall (o6)
    (implies
     (avl-bal-t2-p o6)
     (implies
      (avl-bal-built-p o6 lrr d r)
      (and
       (avl-bal-within-p
        (avl-bal-height ll)
        (avl-bal-height lrl))
       (avl-bal-left-double-outer-universal-p
        ll ld lrl o6))))))

(defun avl-bal-left-double-view-conclusion-p
  (view ll ld r d)
  (if (avl-bal-view-empty-p view)
      nil
    (let ((lrl (avl-bal-view-left view))
          (lrr (avl-bal-view-right view)))
      (and
       (avl-bal-within-p
        (avl-bal-height lrr)
        (avl-bal-height r))
       (avl-bal-left-double-inner-universal-p
        ll ld lrl lrr r d)))))

(defun-sk avl-bal-left-double-universal-p
  (ll ld lr r d)
  (forall (view)
    (implies
     (and
      (avl-bal-view-p view)
      (avl-bal-view-describes-p view lr))
     (avl-bal-left-double-view-conclusion-p
      view ll ld r d))))

(defun avl-bal-left-node-heights-branch-p
  (o3 o4 ll ld lr r d)
  (if (<= o3 o4)
      (and
       (avl-bal-within-p
        (avl-bal-height lr)
        (avl-bal-height r))
       (avl-bal-left-single-universal-p
        ll lr r d))
    (avl-bal-left-double-universal-p
     ll ld lr r d)))

(defun-sk avl-bal-left-node-universal-p
  (ll ld lr r d)
  (forall (o3 o4)
    (implies
     (and
      (integerp o3)
      (equal o3 (avl-bal-height lr))
      (integerp o4)
      (equal o4 (avl-bal-height ll)))
     (avl-bal-left-node-heights-branch-p
      o3 o4 ll ld lr r d))))

(defun avl-bal-left-view-conclusion-p (view r d)
  (if (avl-bal-view-empty-p view)
      nil
    (avl-bal-left-node-universal-p
     (avl-bal-view-left view)
     (avl-bal-view-datum view)
     (avl-bal-view-right view)
     r d)))

(defun-sk avl-bal-left-operational-p (l r d)
  (forall (view)
    (implies
     (and
      (avl-bal-view-p view)
      (avl-bal-view-describes-p view l))
     (avl-bal-left-view-conclusion-p
      view r d))))

;; Universal obligations for the right-heavy single-rotation branch.

(defun-sk avl-bal-right-single-universal-p (l rl rr d)
  (forall (o6)
    (implies
     (avl-bal-t2-p o6)
     (implies
      (avl-bal-built-p o6 l d rl)
      (avl-bal-within-p
       (avl-bal-height o6)
       (avl-bal-height rr))))))

;; Universal obligations for the right-heavy double-rotation branch.

(defun-sk avl-bal-right-double-outer-universal-p
  (l d rll o7)
  (forall (o8)
    (implies
     (avl-bal-t2-p o8)
     (implies
      (avl-bal-built-p o8 l d rll)
      (avl-bal-within-p
       (avl-bal-height o8)
       (avl-bal-height o7))))))

(defun-sk avl-bal-right-double-inner-universal-p
  (l d rll rlr rd rr)
  (forall (o7)
    (implies
     (avl-bal-t2-p o7)
     (implies
      (avl-bal-built-p o7 rlr rd rr)
      (and
       (avl-bal-within-p
        (avl-bal-height l)
        (avl-bal-height rll))
       (avl-bal-right-double-outer-universal-p
        l d rll o7))))))

(defun avl-bal-right-double-view-conclusion-p
  (view l d rd rr)
  (if (avl-bal-view-empty-p view)
      nil
    (let ((rll (avl-bal-view-left view))
          (rlr (avl-bal-view-right view)))
      (and
       (avl-bal-within-p
        (avl-bal-height rlr)
        (avl-bal-height rr))
       (avl-bal-right-double-inner-universal-p
        l d rll rlr rd rr)))))

(defun-sk avl-bal-right-double-universal-p
  (l d rl rd rr)
  (forall (view)
    (implies
     (and
      (avl-bal-view-p view)
      (avl-bal-view-describes-p view rl))
     (avl-bal-right-double-view-conclusion-p
      view l d rd rr))))

(defun avl-bal-right-node-heights-branch-p
  (o4 o5 l d rl rd rr)
  (if (<= o4 o5)
      (and
       (avl-bal-within-p
        (avl-bal-height l)
        (avl-bal-height rl))
       (avl-bal-right-single-universal-p
        l rl rr d))
    (avl-bal-right-double-universal-p
     l d rl rd rr)))

(defun-sk avl-bal-right-node-universal-p
  (l d rl rd rr)
  (forall (o4 o5)
    (implies
     (and
      (integerp o4)
      (equal o4 (avl-bal-height rl))
      (integerp o5)
      (equal o5 (avl-bal-height rr)))
     (avl-bal-right-node-heights-branch-p
      o4 o5 l d rl rd rr))))

(defun avl-bal-right-view-conclusion-p (view l d)
  (if (avl-bal-view-empty-p view)
      nil
    (avl-bal-right-node-universal-p
     l d
     (avl-bal-view-left view)
     (avl-bal-view-datum view)
     (avl-bal-view-right view))))

(defun-sk avl-bal-right-operational-p (l r d)
  (forall (view)
    (implies
     (and
      (avl-bal-view-p view)
      (avl-bal-view-describes-p view r))
     (avl-bal-right-view-conclusion-p
      view l d))))

(defun-sk avl-bal-nonleft-operational-p (df l r d)
  (forall (o2)
    (implies
     (and
      (integerp o2)
      (equal o2 (- (avl-bal-balancing))))
     (if (< df o2)
         (avl-bal-right-operational-p l r d)
       (avl-bal-within-p
        (avl-bal-height l)
        (avl-bal-height r))))))

;; Existential descriptions of the result built by each rotation branch.

(defun-sk avl-bal-left-single-result-p
  (result ll ld lr r d)
  (exists (o5)
    (and
     (avl-bal-t2-p o5)
     (avl-bal-built-p o5 lr d r)
     (avl-bal-built-p result ll ld o5))))

(defun-sk avl-bal-left-double-result-p
  (result ll ld lr r d)
  (exists (view o6 o7)
    (and
     (avl-bal-view-p view)
     (avl-bal-view-describes-p view lr)
     (not (avl-bal-view-empty-p view))
     (avl-bal-t2-p o6)
     (avl-bal-built-p
      o6
      (avl-bal-view-right view)
      d r)
     (avl-bal-t2-p o7)
     (avl-bal-built-p
      o7 ll ld
      (avl-bal-view-left view))
     (avl-bal-built-p
      result o7
      (avl-bal-view-datum view)
      o6))))

(defun-sk avl-bal-left-result-p (result l r d)
  (exists (view o3 o4)
    (and
     (avl-bal-view-p view)
     (avl-bal-view-describes-p view l)
     (not (avl-bal-view-empty-p view))
     (integerp o3)
     (equal
      o3
      (avl-bal-height
       (avl-bal-view-right view)))
     (integerp o4)
     (equal
      o4
      (avl-bal-height
       (avl-bal-view-left view)))
     (if (<= o3 o4)
         (avl-bal-left-single-result-p
          result
          (avl-bal-view-left view)
          (avl-bal-view-datum view)
          (avl-bal-view-right view)
          r d)
       (avl-bal-left-double-result-p
        result
        (avl-bal-view-left view)
        (avl-bal-view-datum view)
        (avl-bal-view-right view)
        r d)))))

(defun-sk avl-bal-right-single-result-p
  (result l d rl rd rr)
  (exists (o6)
    (and
     (avl-bal-t2-p o6)
     (avl-bal-built-p o6 l d rl)
     (avl-bal-built-p result o6 rd rr))))

(defun-sk avl-bal-right-double-result-p
  (result l d rl rd rr)
  (exists (view o7 o8)
    (and
     (avl-bal-view-p view)
     (avl-bal-view-describes-p view rl)
     (not (avl-bal-view-empty-p view))
     (avl-bal-t2-p o7)
     (avl-bal-built-p
      o7
      (avl-bal-view-right view)
      rd rr)
     (avl-bal-t2-p o8)
     (avl-bal-built-p
      o8 l d
      (avl-bal-view-left view))
     (avl-bal-built-p
      result o8
      (avl-bal-view-datum view)
      o7))))

(defun-sk avl-bal-right-result-p (result l r d)
  (exists (view o4 o5)
    (and
     (avl-bal-view-p view)
     (avl-bal-view-describes-p view r)
     (not (avl-bal-view-empty-p view))
     (integerp o4)
     (equal
      o4
      (avl-bal-height
       (avl-bal-view-left view)))
     (integerp o5)
     (equal
      o5
      (avl-bal-height
       (avl-bal-view-right view)))
     (if (<= o4 o5)
         (avl-bal-right-single-result-p
          result l d
          (avl-bal-view-left view)
          (avl-bal-view-datum view)
          (avl-bal-view-right view))
       (avl-bal-right-double-result-p
        result l d
        (avl-bal-view-left view)
        (avl-bal-view-datum view)
        (avl-bal-view-right view))))))

(defun-sk avl-bal-nonleft-result-p (df result l r d)
  (exists (o2)
    (and
     (integerp o2)
     (equal o2 (- (avl-bal-balancing)))
     (if (< df o2)
         (avl-bal-right-result-p result l r d)
       (avl-bal-built-p result l d r)))))

(defun avl-bal-final-result-p (result l r d)
  (let* ((left-height (avl-bal-height l))
         (right-height (avl-bal-height r))
         (expected-height
          (+ 1
             (avl-bal-max
              left-height right-height)))
         (result-height (avl-bal-height result))
         (height-error
          (- expected-height result-height)))
    (and
     (equal
      (avl-bal-sequence result)
      (avl-bal-node-model
       (avl-bal-sequence l)
       d
       (avl-bal-sequence r)))
     (<= 0 height-error)
     (<= height-error 1)
     (implies
      (avl-bal-within-p
       left-height right-height)
      (equal expected-height result-height)))))

(defun-sk avl-bal-result-obligation-p (df l r d)
  (forall (result)
    (implies
     (avl-bal-t2-p result)
     (implies
      (if (< (avl-bal-balancing) df)
          (avl-bal-left-result-p
           result l r d)
        (avl-bal-nonleft-result-p
         df result l r d))
      (avl-bal-final-result-p
       result l r d)))))

(defun avl-bal-df-body-p (df l r d)
  (and
   (if (< (avl-bal-balancing) df)
       (avl-bal-left-operational-p l r d)
     (avl-bal-nonleft-operational-p
      df l r d))
   (avl-bal-result-obligation-p
    df l r d)))

(defun-sk avl-bal-df-obligation-p (l r hl hr d)
  (forall (df)
    (implies
     (and
      (integerp df)
      (equal df (- hl hr)))
     (avl-bal-df-body-p
      df l r d))))

(defun avl-bal-conclusion-p (l r hl hr o1 d)
  (and
   (<= o1 (- hl hr))
   (<= (- hl hr) hl)
   (avl-bal-df-obligation-p
    l r hl hr d)))

(defun-sk ntp4vc-pearl-avl-avl-balanceqtvc-statement ()
  (forall (l r hl hr o1 d)
    (implies
     (and
      (avl-bal-background-p)
      (avl-bal-t2-p l)
      (avl-bal-t2-p r)
      (integerp hl)
      (integerp hr)
      (integerp o1)
      (avl-bal-t1-p d)
      (<=
       (- (- (avl-bal-balancing)) 1)
       (- (avl-bal-height l)
          (avl-bal-height r)))
      (<=
       (- (avl-bal-height l)
          (avl-bal-height r))
       (+ (avl-bal-balancing) 1))
      (equal hl (avl-bal-height l))
      (equal hr (avl-bal-height r))
      (equal o1 (- hr)))
     (avl-bal-conclusion-p
      l r hl hr o1 d))))

(value-triple :itpeval-statement-checked)
:q
