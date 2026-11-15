;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/avl_AVL_joinqtvc: the AVL join verification condition for
;; sequence preservation and bounded height change through rebalancing.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the arbitrary source carriers t, t1 alpha,
;; and t2 alpha at a fixed arbitrary inhabited alpha.

(defstub avlj-t-p (x) t)
(defstub avlj-t1-p (x) t)
(defstub avlj-t2-p (x) t)

(defstub avlj-zero () t)
(defstub avlj-op (left right) t)
(defstub avlj-measure (datum) t)
(defstub avlj-measure-closure (datum) t)
(defstub avlj-aggregate (sequence) t)
(defstub avlj-balancing () t)
(defstub avlj-repr (object) t)
(defstub avlj-m1 (object) t)

(defun avlj-t1-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (avlj-t1-p (car xs))
     (avlj-t1-list-p (cdr xs)))))

;; Empty trees are NIL. Nodes are exact records
;; (:TREE-NODE left datum right height summary).

(defun avlj-tree-empty-p (tree)
  (equal tree nil))

(defun avlj-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun avlj-tree-left (tree)
  (cadr tree))

(defun avlj-tree-datum (tree)
  (caddr tree))

(defun avlj-tree-right (tree)
  (cadddr tree))

(defun avlj-tree-height (tree)
  (car (cddddr tree)))

(defun avlj-tree-summary (tree)
  (cadr (cddddr tree)))

(defun avlj-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlj-tree-empty-p tree)
      t
    (and
     (avlj-tree-node-shape-p tree)
     (avlj-tree-p (avlj-tree-left tree))
     (avlj-t1-p (avlj-tree-datum tree))
     (avlj-tree-p (avlj-tree-right tree))
     (natp (avlj-tree-height tree))
     (avlj-t-p (avlj-tree-summary tree)))))

;; The source model record m is represented exactly as
;; (:M sequence integer-height).

(defun avlj-m-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (avlj-t1-list-p (cadr model))
   (integerp (caddr model))))

(defun avlj-m-seq (model)
  (cadr model))

(defun avlj-m-hgt (model)
  (caddr model))

(defun avlj-node-model (left datum right)
  (append left (cons datum right)))

(defun avlj-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlj-tree-empty-p tree)
      nil
    (if (avlj-tree-node-shape-p tree)
        (avlj-node-model
         (avlj-seq-model (avlj-tree-left tree))
         (avlj-tree-datum tree)
         (avlj-seq-model (avlj-tree-right tree)))
      nil)))

(defun avlj-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlj-tree-empty-p tree)
      0
    (if (avlj-tree-node-shape-p tree)
        (let ((left-height
               (avlj-real-height
                (avlj-tree-left tree)))
              (right-height
               (avlj-real-height
                (avlj-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun avlj-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (avlj-tree-empty-p tree)
      t
    (if (avlj-tree-node-shape-p tree)
        (let* ((left (avlj-tree-left tree))
               (right (avlj-tree-right tree))
               (height (avlj-tree-height tree))
               (summary (avlj-tree-summary tree))
               (difference
                (- (avlj-real-height right)
                   (avlj-real-height left))))
          (and
           (equal height (avlj-real-height tree))
           (equal
            summary
            (avlj-aggregate
             (avlj-seq-model tree)))
           (<= (- (avlj-balancing)) difference)
           (<= difference (avlj-balancing))
           (avlj-balanced-p left)
           (avlj-balanced-p right)))
      nil)))

;; Empty views are NIL. Nodes are exact records
;; (:VIEW-NODE left datum right height summary).

(defun avlj-view-empty-p (view)
  (equal view nil))

(defun avlj-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun avlj-view-left (view)
  (cadr view))

(defun avlj-view-datum (view)
  (caddr view))

(defun avlj-view-right (view)
  (cadddr view))

(defun avlj-view-height (view)
  (car (cddddr view)))

(defun avlj-view-summary (view)
  (cadr (cddddr view)))

(defun avlj-view-p (view)
  (or
   (avlj-view-empty-p view)
   (and
    (avlj-view-node-shape-p view)
    (avlj-t2-p (avlj-view-left view))
    (avlj-t1-p (avlj-view-datum view))
    (avlj-t2-p (avlj-view-right view))
    (natp (avlj-view-height view))
    (avlj-t-p (avlj-view-summary view)))))

;; The source carrier, algebra, aggregate, positivity, representation
;; invariant, and injectivity assumptions remain explicit hypotheses.

(defun-sk avlj-carriers-inhabited-p ()
  (exists (datum object)
    (and
     (avlj-t1-p datum)
     (avlj-t2-p object))))

(defun-sk avlj-function-closures-p ()
  (forall (left right datum sequence object)
    (and
     (implies
      (and
       (avlj-t-p left)
       (avlj-t-p right))
      (avlj-t-p
       (avlj-op left right)))
     (implies
      (avlj-t1-p datum)
      (and
       (avlj-t-p
        (avlj-measure datum))
       (avlj-t-p
        (avlj-measure-closure datum))))
     (implies
      (avlj-t1-list-p sequence)
      (avlj-t-p
       (avlj-aggregate sequence)))
     (implies
      (avlj-t2-p object)
      (and
       (avlj-tree-p
        (avlj-repr object))
       (avlj-m-p
        (avlj-m1 object)))))))

(defun-sk avlj-associative-p ()
  (forall (a b c)
    (implies
     (and
      (avlj-t-p a)
      (avlj-t-p b)
      (avlj-t-p c))
     (equal
      (avlj-op a (avlj-op b c))
      (avlj-op (avlj-op a b) c)))))

(defun-sk avlj-neutral-p ()
  (forall (x)
    (implies
     (avlj-t-p x)
     (and
      (equal
       (avlj-op x (avlj-zero))
       x)
      (equal
       x
       (avlj-op (avlj-zero) x))))))

(defun-sk avlj-aggregate-singleton-law-p ()
  (forall (sequence)
    (implies
     (and
      (avlj-t1-list-p sequence)
      (equal (len sequence) 1))
     (equal
      (avlj-aggregate sequence)
      (avlj-measure-closure
       (car sequence))))))

(defun-sk avlj-aggregate-concatenation-law-p ()
  (forall (left right)
    (implies
     (and
      (avlj-t1-list-p left)
      (avlj-t1-list-p right))
     (equal
      (avlj-aggregate
       (append left right))
      (avlj-op
       (avlj-aggregate left)
       (avlj-aggregate right))))))

(defun-sk avlj-measure-closure-law-p ()
  (forall (datum)
    (implies
     (avlj-t1-p datum)
     (equal
      (avlj-measure-closure datum)
      (avlj-measure datum)))))

(defun-sk avlj-invariant-p ()
  (forall (object)
    (implies
     (avlj-t2-p object)
     (let ((tree (avlj-repr object))
           (model (avlj-m1 object)))
       (and
        (avlj-balanced-p tree)
        (equal
         (avlj-m-seq model)
         (avlj-seq-model tree))
        (equal
         (avlj-m-hgt model)
         (avlj-real-height tree)))))))

(defun-sk avlj-t2-injective-p ()
  (forall (left right)
    (implies
     (and
      (avlj-t2-p left)
      (avlj-t2-p right)
      (equal
       (avlj-repr left)
       (avlj-repr right))
      (equal
       (avlj-m1 left)
       (avlj-m1 right)))
     (equal left right))))

(defun avlj-background-p ()
  (and
   (avlj-t-p (avlj-zero))
   (natp (avlj-balancing))
   (< 0 (avlj-balancing))
   (avlj-carriers-inhabited-p)
   (avlj-function-closures-p)
   (avlj-associative-p)
   (avlj-neutral-p)
   (equal
    (avlj-aggregate nil)
    (avlj-zero))
   (avlj-aggregate-singleton-law-p)
   (avlj-aggregate-concatenation-law-p)
   (avlj-measure-closure-law-p)
   (avlj-invariant-p)
   (avlj-t2-injective-p)))

(defun avlj-sequence (object)
  (avlj-m-seq
   (avlj-m1 object)))

(defun avlj-height (object)
  (avlj-m-hgt
   (avlj-m1 object)))

(defun avlj-max (left right)
  (if (< left right)
      right
    left))

(defun avlj-within-p (left-height right-height)
  (let ((difference (- left-height right-height)))
    (and
     (<= (- (avlj-balancing)) difference)
     (<= difference (avlj-balancing)))))

(defun avlj-absolute-difference (left right)
  (if (< left right)
      (- right left)
    (- left right)))

(defun avlj-view-describes-p (view object)
  (if (avlj-view-empty-p view)
      (and
       (equal (avlj-height object) 0)
       (equal (avlj-sequence object) nil))
    (let* ((left (avlj-view-left view))
           (right (avlj-view-right view))
           (datum (avlj-view-datum view))
           (height (avlj-view-height view))
           (summary (avlj-view-summary view))
           (left-height (avlj-height left))
           (right-height (avlj-height right)))
      (and
       (equal
        (avlj-sequence object)
        (avlj-node-model
         (avlj-sequence left)
         datum
         (avlj-sequence right)))
       (equal
        summary
        (avlj-aggregate
         (avlj-sequence object)))
       (avlj-within-p left-height right-height)
       (equal (avlj-height object) height)
       (equal
        height
        (+ 1
           (avlj-max left-height right-height)))))))

(defun avlj-near-node-p (object left datum right)
  (let* ((expected-height
          (+ 1
             (avlj-max
              (avlj-height left)
              (avlj-height right))))
         (height-error
          (- expected-height
             (avlj-height object))))
    (and
     (equal
      (avlj-sequence object)
      (avlj-node-model
       (avlj-sequence left)
       datum
       (avlj-sequence right)))
     (<= 0 height-error)
     (<= height-error 1))))

(defun avlj-near-node-with-balance-exact-p
  (object left datum right)
  (let ((expected-height
         (+ 1
            (avlj-max
             (avlj-height left)
             (avlj-height right)))))
    (and
     (avlj-near-node-p object left datum right)
     (implies
      (avlj-within-p
       (avlj-height left)
       (avlj-height right))
      (equal expected-height
             (avlj-height object))))))

;; Universal obligations in the two recursive join branches.

(defun-sk avlj-left-recursive-universal-p (ll lr r d)
  (forall (o4)
    (implies
     (avlj-t2-p o4)
     (implies
      (avlj-near-node-p o4 lr d r)
      (let ((difference
             (- (avlj-height ll)
                (avlj-height o4))))
        (and
         (<= (- (- (avlj-balancing)) 1)
             difference)
         (<= difference
             (+ (avlj-balancing) 1))))))))

(defun-sk avlj-right-recursive-universal-p (l rl rr d)
  (forall (o5)
    (implies
     (avlj-t2-p o5)
     (implies
      (avlj-near-node-p o5 l d rl)
      (let ((difference
             (- (avlj-height o5)
                (avlj-height rr))))
        (and
         (<= (- (- (avlj-balancing)) 1)
             difference)
         (<= difference
             (+ (avlj-balancing) 1))))))))

(defun-sk avlj-operational-negative-bound-p
  (df l r rl rr d)
  (forall (o4)
    (implies
     (and
      (integerp o4)
      (equal o4 (- (avlj-balancing))))
     (if (< df o4)
         (and
          (<= 0
              (avlj-absolute-difference
               (avlj-height r)
               (avlj-height l)))
          (< (avlj-absolute-difference
              (avlj-height rl)
              (avlj-height l))
             (avlj-absolute-difference
              (avlj-height r)
              (avlj-height l)))
          (avlj-right-recursive-universal-p
           l rl rr d))
       (avlj-within-p
        (avlj-height l)
        (avlj-height r))))))

(defun avlj-operational-df-branch-p
  (df ll lr l r rl rr d)
  (if (< (avlj-balancing) df)
      (and
       (<= 0
           (avlj-absolute-difference
            (avlj-height r)
            (avlj-height l)))
       (< (avlj-absolute-difference
           (avlj-height r)
           (avlj-height lr))
          (avlj-absolute-difference
           (avlj-height r)
           (avlj-height l)))
       (avlj-left-recursive-universal-p
        ll lr r d))
    (avlj-operational-negative-bound-p
     df l r rl rr d)))

(defun-sk avlj-operational-df-universal-p
  (lh rh ll lr l r rl rr d)
  (forall (df)
    (implies
     (and
      (integerp df)
      (equal df (- lh rh)))
     (avlj-operational-df-branch-p
      df ll lr l r rl rr d))))

(defun avlj-operational-o3-body-p
  (o3 lh rh ll lr l r rl rr d)
  (and
   (<= o3 (- lh rh))
   (<= (- lh rh) lh)
   (avlj-operational-df-universal-p
    lh rh ll lr l r rl rr d)))

(defun-sk avlj-operational-o3-universal-p
  (lh rh ll lr l r rl rr d)
  (forall (o3)
    (implies
     (and
      (integerp o3)
      (equal o3 (- rh)))
     (avlj-operational-o3-body-p
      o3 lh rh ll lr l r rl rr d))))

(defun avlj-operational-right-view-conclusion-p
  (view lh ll lr l r d)
  (if (avlj-view-empty-p view)
      t
    (avlj-operational-o3-universal-p
     lh
     (avlj-view-height view)
     ll lr l r
     (avlj-view-left view)
     (avlj-view-right view)
     d)))

(defun-sk avlj-operational-right-view-universal-p
  (lh ll lr l r d)
  (forall (view)
    (implies
     (avlj-view-p view)
     (implies
      (avlj-view-describes-p view r)
      (avlj-operational-right-view-conclusion-p
       view lh ll lr l r d)))))

(defun avlj-operational-conclusion-p (o1 l r d)
  (if (avlj-view-empty-p o1)
      t
    (avlj-operational-right-view-universal-p
     (avlj-view-height o1)
     (avlj-view-left o1)
     (avlj-view-right o1)
     l r d)))

;; Existential descriptions of the result in each operational branch.

(defun-sk avlj-left-recursive-result-p
  (result ll ld lr r d)
  (exists (o4)
    (and
     (avlj-t2-p o4)
     (avlj-near-node-p o4 lr d r)
     (avlj-near-node-with-balance-exact-p
      result ll ld o4))))

(defun-sk avlj-right-recursive-result-p
  (result l rl rd rr d)
  (exists (o5)
    (and
     (avlj-t2-p o5)
     (avlj-near-node-p o5 l d rl)
     (avlj-near-node-with-balance-exact-p
      result o5 rd rr))))

(defun-sk avlj-result-negative-bound-p
  (df result l r rl rd rr d)
  (exists (o4)
    (and
     (integerp o4)
     (equal o4 (- (avlj-balancing)))
     (if (< df o4)
         (avlj-right-recursive-result-p
          result l rl rd rr d)
       (and
        (equal
         (avlj-sequence result)
         (avlj-node-model
          (avlj-sequence l)
          d
          (avlj-sequence r)))
        (equal
         (avlj-height result)
         (+ 1
            (avlj-max
             (avlj-height l)
             (avlj-height r)))))))))

(defun avlj-result-df-branch-p
  (df result ll ld lr l r rl rd rr d)
  (if (< (avlj-balancing) df)
      (avlj-left-recursive-result-p
       result ll ld lr r d)
    (avlj-result-negative-bound-p
     df result l r rl rd rr d)))

(defun-sk avlj-result-df-exists-p
  (result lh rh ll ld lr l r rl rd rr d)
  (exists (df)
    (and
     (integerp df)
     (equal df (- lh rh))
     (avlj-result-df-branch-p
      df result ll ld lr l r rl rd rr d))))

(defun-sk avlj-result-o3-exists-p
  (result lh rh ll ld lr l r rl rd rr d)
  (exists (o3)
    (and
     (integerp o3)
     (equal o3 (- rh))
     (avlj-result-df-exists-p
      result lh rh ll ld lr l r rl rd rr d))))

(defun avlj-result-right-view-conclusion-p
  (view result lh ll ld lr l r d)
  (if (avlj-view-empty-p view)
      (let ((difference
             (- (avlj-height result)
                (avlj-height l))))
        (and
         (equal
          (avlj-sequence result)
          (append
           (avlj-sequence l)
           (list d)))
         (<= difference 1)
         (<= 0 difference)))
    (avlj-result-o3-exists-p
     result lh
     (avlj-view-height view)
     ll ld lr l r
     (avlj-view-left view)
     (avlj-view-datum view)
     (avlj-view-right view)
     d)))

(defun-sk avlj-result-node-premise-p
  (result lh ll ld lr l r d)
  (exists (view)
    (and
     (avlj-view-p view)
     (avlj-view-describes-p view r)
     (avlj-result-right-view-conclusion-p
      view result lh ll ld lr l r d))))

(defun avlj-result-premise-p (result o1 l r d)
  (if (avlj-view-empty-p o1)
      (let ((difference
             (- (avlj-height result)
                (avlj-height r))))
        (and
         (equal
          (avlj-sequence result)
          (cons d
                (avlj-sequence r)))
         (<= difference 1)
         (<= 0 difference)))
    (avlj-result-node-premise-p
     result
     (avlj-view-height o1)
     (avlj-view-left o1)
     (avlj-view-datum o1)
     (avlj-view-right o1)
     l r d)))

(defun avlj-final-result-p (result l r d)
  (let* ((expected-height
          (+ 1
             (avlj-max
              (avlj-height l)
              (avlj-height r))))
         (height-error
          (- expected-height
             (avlj-height result))))
    (and
     (equal
      (avlj-sequence result)
      (avlj-node-model
       (avlj-sequence l)
       d
       (avlj-sequence r)))
     (<= 0 height-error)
     (<= height-error 1))))

(defun-sk avlj-result-continuation-p (o1 l r d)
  (forall (result)
    (implies
     (avlj-t2-p result)
     (implies
      (avlj-result-premise-p result o1 l r d)
      (avlj-final-result-p result l r d)))))

(defun avlj-conclusion-p (o1 l r d)
  (and
   (avlj-operational-conclusion-p o1 l r d)
   (avlj-result-continuation-p o1 l r d)))

(defun-sk ntp4vc-pearl-avl-avl-joinqtvc-statement ()
  (forall (o1 l r d)
    (implies
     (and
      (avlj-background-p)
      (avlj-view-p o1)
      (avlj-t2-p l)
      (avlj-t2-p r)
      (avlj-t1-p d)
      (avlj-view-describes-p o1 l))
     (avlj-conclusion-p o1 l r d))))

(value-triple :itpeval-statement-checked)
:q
