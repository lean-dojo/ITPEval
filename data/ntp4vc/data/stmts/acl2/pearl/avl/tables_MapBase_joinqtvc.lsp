;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/tables_MapBase_joinqtvc: the AVL-map join verification condition
;; preserving sorted key order, side lookups, the pivot binding, cardinality,
;; and the bounded result-height error. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent one fixed arbitrary inhabited
;; source parameter type and its associated item, key, tree-object, and map
;; carriers.  Every source law is explicit in the statement context.

(defstub mapjoin-item-p (x) t)
(defstub mapjoin-key-p (x) t)
(defstub mapjoin-key (item) t)
(defstub mapjoin-le (left right) t)
(defstub mapjoin-balancing () t)

(defstub mapjoin-tree-object-p (x) t)
(defstub mapjoin-repr (object) t)
(defstub mapjoin-model-sequence (object) t)
(defstub mapjoin-model-height (object) t)

(defstub mapjoin-map-p (x) t)
(defstub mapjoin-field (map) t)
(defstub mapjoin-make-function (sequence key) t)

(defun mapjoin-item-list-p (sequence)
  (if (consp sequence)
      (and
       (mapjoin-item-p (car sequence))
       (mapjoin-item-list-p (cdr sequence)))
    (equal sequence nil)))

(defun mapjoin-key-eq-p (left right)
  (and
   (mapjoin-le left right)
   (mapjoin-le right left)))

(defun mapjoin-key-lt-p (left right)
  (and
   (mapjoin-le left right)
   (not (mapjoin-le right left))))

(defun mapjoin-nth-item (index sequence)
  (nth (nfix index) sequence))

(defun-sk mapjoin-selection-possible-p (sequence)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j)
      (<= 0 i)
      (< i j)
      (< j (len sequence)))
     (mapjoin-key-lt-p
      (mapjoin-key
       (mapjoin-nth-item i sequence))
      (mapjoin-key
       (mapjoin-nth-item j sequence))))))

(defun mapjoin-node-model (left item right)
  (append left (cons item right)))

;; Unit is a singleton, so omitting the source node's unit-valued field gives
;; a definitional bijection with :EMPTY and
;; (:NODE left item right stored-height).

(defun mapjoin-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 5)
   (equal (car tree) :node)))

(defun mapjoin-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (or
   (equal tree :empty)
   (and
    (mapjoin-node-shape-p tree)
    (mapjoin-tree-p (cadr tree))
    (mapjoin-item-p (caddr tree))
    (mapjoin-tree-p (cadddr tree))
    (natp (car (cddddr tree))))))

(defun mapjoin-tree-left (tree)
  (cadr tree))

(defun mapjoin-tree-item (tree)
  (caddr tree))

(defun mapjoin-tree-right (tree)
  (cadddr tree))

(defun mapjoin-tree-stored-height (tree)
  (car (cddddr tree)))

(defun mapjoin-sequence-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (mapjoin-node-shape-p tree))
      nil
    (mapjoin-node-model
     (mapjoin-sequence-model
      (mapjoin-tree-left tree))
     (mapjoin-tree-item tree)
     (mapjoin-sequence-model
      (mapjoin-tree-right tree)))))

(defun mapjoin-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (mapjoin-node-shape-p tree))
      0
    (let ((left-height
           (mapjoin-real-height
            (mapjoin-tree-left tree)))
          (right-height
           (mapjoin-real-height
            (mapjoin-tree-right tree))))
      (+ 1
         (if (< left-height right-height)
             right-height
           left-height)))))

(defun mapjoin-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (mapjoin-node-shape-p tree))
      t
    (let* ((left (mapjoin-tree-left tree))
           (right (mapjoin-tree-right tree))
           (difference
            (- (mapjoin-real-height right)
               (mapjoin-real-height left))))
      (and
       (equal
        (mapjoin-tree-stored-height tree)
        (mapjoin-real-height tree))
       (<= (- (mapjoin-balancing)) difference)
       (<= difference (mapjoin-balancing))
       (mapjoin-balanced-p left)
       (mapjoin-balanced-p right)))))

;; The source domain keeps its existential witness internal.

(defun-sk mapjoin-domain-p (sequence key)
  (exists (i)
    (and
     (integerp i)
     (<= 0 i)
     (< i (len sequence))
     (mapjoin-key-eq-p
      (mapjoin-key
       (mapjoin-nth-item i sequence))
      key))))

;; The ambient source declarations become explicit hypotheses.  The arbitrary
;; carriers remain potentially infinite.

(defun-sk mapjoin-carriers-inhabited-p ()
  (exists (item key tree-object map)
    (and
     (mapjoin-item-p item)
     (mapjoin-key-p key)
     (mapjoin-tree-object-p tree-object)
     (mapjoin-map-p map))))

(defun-sk mapjoin-key-and-order-laws-p ()
  (forall (item x y z)
    (and
     (implies
      (mapjoin-item-p item)
      (mapjoin-key-p
       (mapjoin-key item)))
     (implies
      (mapjoin-key-p x)
      (mapjoin-le x x))
     (implies
      (and
       (mapjoin-key-p x)
       (mapjoin-key-p y)
       (mapjoin-key-p z)
       (mapjoin-le x y)
       (mapjoin-le y z))
      (mapjoin-le x z))
     (implies
      (and
       (mapjoin-key-p x)
       (mapjoin-key-p y))
      (or
       (mapjoin-le x y)
       (mapjoin-le y x))))))

(defun-sk mapjoin-tree-object-laws-p ()
  (forall (self left right)
    (and
     (implies
      (mapjoin-tree-object-p self)
      (and
       (mapjoin-tree-p
        (mapjoin-repr self))
       (mapjoin-balanced-p
        (mapjoin-repr self))
       (mapjoin-item-list-p
        (mapjoin-model-sequence self))
       (equal
        (mapjoin-model-sequence self)
        (mapjoin-sequence-model
         (mapjoin-repr self)))
       (integerp
        (mapjoin-model-height self))
       (equal
        (mapjoin-model-height self)
        (mapjoin-real-height
         (mapjoin-repr self)))))
     (implies
      (and
       (mapjoin-tree-object-p left)
       (mapjoin-tree-object-p right)
       (equal
        (mapjoin-repr left)
        (mapjoin-repr right))
       (equal
        (mapjoin-model-sequence left)
        (mapjoin-model-sequence right))
       (equal
        (mapjoin-model-height left)
        (mapjoin-model-height right)))
      (equal left right)))))

(defun-sk mapjoin-map-laws-p ()
  (forall (self left right)
    (and
     (implies
      (mapjoin-map-p self)
      (and
       (mapjoin-tree-object-p
        (mapjoin-field self))
       (mapjoin-selection-possible-p
        (mapjoin-model-sequence
         (mapjoin-field self)))))
     (implies
      (and
       (mapjoin-map-p left)
       (mapjoin-map-p right)
       (equal
        (mapjoin-field left)
        (mapjoin-field right)))
      (equal left right)))))

(defun-sk mapjoin-make-function-laws-p ()
  (forall (sequence key i)
    (and
     (implies
      (and
       (mapjoin-item-list-p sequence)
       (mapjoin-key-p key))
      (mapjoin-item-p
       (mapjoin-make-function sequence key)))
     (implies
      (and
       (mapjoin-item-list-p sequence)
       (mapjoin-key-p key)
       (integerp i)
       (mapjoin-selection-possible-p sequence)
       (mapjoin-domain-p sequence key)
       (<= 0 i)
       (< i (len sequence))
       (mapjoin-key-eq-p
        (mapjoin-key
         (mapjoin-nth-item i sequence))
        key))
      (equal
       (mapjoin-make-function sequence key)
       (mapjoin-nth-item i sequence))))))

(defun mapjoin-context-p ()
  (and
   (natp (mapjoin-balancing))
   (< 0 (mapjoin-balancing))
   (mapjoin-carriers-inhabited-p)
   (mapjoin-key-and-order-laws-p)
   (mapjoin-tree-object-laws-p)
   (mapjoin-map-laws-p)
   (mapjoin-make-function-laws-p)))

;; These accessors definitionally reduce the source m3 record using
;; domain_closure_def and make_func_closure_def.

(defun mapjoin-map-sequence (map)
  (mapjoin-model-sequence
   (mapjoin-field map)))

(defun mapjoin-map-domain-p (map key)
  (mapjoin-domain-p
   (mapjoin-map-sequence map)
   key))

(defun mapjoin-map-function (map key)
  (mapjoin-make-function
   (mapjoin-map-sequence map)
   key))

(defun mapjoin-map-cardinality (map)
  (len (mapjoin-map-sequence map)))

(defun-sk mapjoin-left-bound-p (left pivot)
  (forall (key)
    (implies
     (and
      (mapjoin-key-p key)
      (mapjoin-map-domain-p left key))
     (mapjoin-key-lt-p key pivot))))

(defun-sk mapjoin-right-bound-p (right pivot)
  (forall (key)
    (implies
     (and
      (mapjoin-key-p key)
      (mapjoin-map-domain-p right key))
     (mapjoin-key-lt-p pivot key))))

(defun-sk mapjoin-left-domain-preserved-p
    (left result pivot)
  (forall (key)
    (implies
     (and
      (mapjoin-key-p key)
      (mapjoin-key-lt-p key pivot))
     (iff
      (mapjoin-map-domain-p result key)
      (mapjoin-map-domain-p left key)))))

(defun-sk mapjoin-left-function-preserved-p
    (left result pivot)
  (forall (key)
    (implies
     (and
      (mapjoin-key-p key)
      (mapjoin-key-lt-p key pivot)
      (mapjoin-map-domain-p result key))
     (equal
      (mapjoin-map-function result key)
      (mapjoin-map-function left key)))))

(defun-sk mapjoin-right-domain-preserved-p
    (right result pivot)
  (forall (key)
    (implies
     (and
      (mapjoin-key-p key)
      (mapjoin-key-lt-p pivot key))
     (iff
      (mapjoin-map-domain-p result key)
      (mapjoin-map-domain-p right key)))))

(defun-sk mapjoin-right-function-preserved-p
    (right result pivot)
  (forall (key)
    (implies
     (and
      (mapjoin-key-p key)
      (mapjoin-key-lt-p pivot key)
      (mapjoin-map-domain-p result key))
     (equal
      (mapjoin-map-function result key)
      (mapjoin-map-function right key)))))

(defun-sk mapjoin-pivot-binding-p
    (result item pivot)
  (forall (key)
    (implies
     (and
      (mapjoin-key-p key)
      (mapjoin-key-eq-p key pivot))
     (and
      (mapjoin-map-domain-p result key)
      (equal
       (mapjoin-map-function result key)
       item)))))

(defun-sk mapjoin-result-postcondition-p
    (left item right tree-result)
  (forall (result)
    (implies
     (and
      (mapjoin-map-p result)
      (equal
       (mapjoin-field result)
       tree-result))
     (let ((pivot (mapjoin-key item)))
       (and
        (mapjoin-left-domain-preserved-p
         left result pivot)
        (mapjoin-left-function-preserved-p
         left result pivot)
        (mapjoin-right-domain-preserved-p
         right result pivot)
        (mapjoin-right-function-preserved-p
         right result pivot)
        (mapjoin-pivot-binding-p
         result item pivot)
        (equal
         (mapjoin-map-cardinality result)
         (+ 1
            (mapjoin-map-cardinality left)
            (mapjoin-map-cardinality right))))))))

(defun mapjoin-height-premise-p
    (left-tree right-tree result-tree)
  (let* ((left-height
          (mapjoin-model-height left-tree))
         (right-height
          (mapjoin-model-height right-tree))
         (expected-height
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
         (height-error
          (- expected-height
             (mapjoin-model-height result-tree))))
    (and
     (<= 0 height-error)
     (<= height-error 1))))

(defun-sk mapjoin-all-tree-results-p (left item right)
  (forall (tree-result)
    (implies
     (and
      (mapjoin-tree-object-p tree-result)
      (equal
       (mapjoin-model-sequence tree-result)
       (mapjoin-node-model
        (mapjoin-map-sequence left)
        item
        (mapjoin-map-sequence right)))
      (mapjoin-height-premise-p
       (mapjoin-field left)
       (mapjoin-field right)
       tree-result))
     (and
      (mapjoin-selection-possible-p
       (mapjoin-model-sequence tree-result))
      (mapjoin-result-postcondition-p
       left item right tree-result)))))

(defun-sk
    ntp4vc-pearl-avl-tables-mapbase-joinqtvc-statement ()
  (forall (left item right)
    (implies
     (and
      (mapjoin-context-p)
      (mapjoin-map-p left)
      (mapjoin-item-p item)
      (mapjoin-map-p right)
      (mapjoin-left-bound-p
       left (mapjoin-key item))
      (mapjoin-right-bound-p
       right (mapjoin-key item)))
     (mapjoin-all-tree-results-p
      left item right))))

(value-triple :itpeval-statement-checked)
:q
