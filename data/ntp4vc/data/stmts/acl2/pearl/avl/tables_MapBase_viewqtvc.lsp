;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/tables_MapBase_viewqtvc: the AVL-backed map view verification
;; condition relating empty and node decompositions to sortedness, cardinality,
;; domain membership, and lookup bindings. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent one fixed arbitrary inhabited source
;; parameter type, its item and key carriers, and the abstract tree-object and
;; map carriers.  All source laws used by the verification condition are
;; explicit in the statement context below.

(defstub mapview-item-p (x) t)
(defstub mapview-key-p (x) t)
(defstub mapview-t2-p (x) t)
(defstub mapview-selector-p (x) t)
(defstub mapview-part-p (x) t)
(defstub mapview-tree-object-p (x) t)
(defstub mapview-map-p (x) t)

(defstub mapview-balancing () t)
(defstub mapview-key (item) t)
(defstub mapview-le-op (left right) t)
(defstub mapview-repr (object) t)
(defstub mapview-m1 (object) t)
(defstub mapview-field (map) t)
(defstub mapview-make-func (sequence key) t)
(defstub mapview-domain-closure (sequence key) t)
(defstub mapview-make-func-closure (sequence key) t)

(defun mapview-le-p (left right)
  (if (mapview-le-op left right) t nil))

(defun mapview-eq-p (left right)
  (and
   (mapview-le-p left right)
   (mapview-le-p right left)))

(defun mapview-lt-p (left right)
  (and
   (mapview-le-p left right)
   (not (mapview-le-p right left))))

(defun mapview-item-list-p (sequence)
  (if (consp sequence)
      (and
       (mapview-item-p (car sequence))
       (mapview-item-list-p (cdr sequence)))
    (equal sequence nil)))

;; The bounded integer-index quantifiers are retained explicitly. Bounds make
;; ACL2's NTH denote the same source list element.

(defun-sk mapview-selection-possible-p (sequence)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j)
      (<= 0 i)
      (< i j)
      (< j (len sequence)))
     (mapview-lt-p
      (mapview-key (nth i sequence))
      (mapview-key (nth j sequence))))))

;; The source tree datatype is represented exactly by (:EMPTY) and
;; (:NODE left item right natural-height :UNIT).

(defun mapview-tree-empty ()
  (list :empty))

(defun mapview-tree-empty-p (tree)
  (equal tree (mapview-tree-empty)))

(defun mapview-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :node)))

(defun mapview-tree-left (tree)
  (cadr tree))

(defun mapview-tree-item (tree)
  (caddr tree))

(defun mapview-tree-right (tree)
  (cadddr tree))

(defun mapview-tree-height (tree)
  (car (cddddr tree)))

(defun mapview-tree-unit (tree)
  (cadr (cddddr tree)))

(defun mapview-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (or
   (mapview-tree-empty-p tree)
   (and
    (mapview-tree-node-shape-p tree)
    (mapview-tree-p (mapview-tree-left tree))
    (mapview-item-p (mapview-tree-item tree))
    (mapview-tree-p (mapview-tree-right tree))
    (natp (mapview-tree-height tree))
    (equal (mapview-tree-unit tree) :unit))))

;; The source model record m is represented by (:M sequence integer-height).

(defun mapview-model-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (mapview-item-list-p (cadr model))
   (integerp (caddr model))))

(defun mapview-model-sequence (model)
  (cadr model))

(defun mapview-model-height (model)
  (caddr model))

(defun mapview-node-model (left item right)
  (append left (cons item right)))

(defun mapview-sequence-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (mapview-tree-empty-p tree)
      nil
    (if (mapview-tree-node-shape-p tree)
        (mapview-node-model
         (mapview-sequence-model
          (mapview-tree-left tree))
         (mapview-tree-item tree)
         (mapview-sequence-model
          (mapview-tree-right tree)))
      nil)))

(defun mapview-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (mapview-tree-empty-p tree)
      0
    (if (mapview-tree-node-shape-p tree)
        (let ((left-height
               (mapview-real-height
                (mapview-tree-left tree)))
              (right-height
               (mapview-real-height
                (mapview-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun mapview-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (mapview-tree-empty-p tree)
      t
    (if (mapview-tree-node-shape-p tree)
        (let* ((left (mapview-tree-left tree))
               (right (mapview-tree-right tree))
               (difference
                (- (mapview-real-height right)
                   (mapview-real-height left))))
          (and
           (equal
            (mapview-tree-height tree)
            (mapview-real-height tree))
           (equal (mapview-tree-unit tree) :unit)
           (<= (- (mapview-balancing)) difference)
           (<= difference (mapview-balancing))
           (mapview-balanced-p left)
           (mapview-balanced-p right)))
      nil)))

;; Domain preserves the source's internal existential integer witness.

(defun-sk mapview-domain-p (sequence key)
  (exists (i)
    (and
     (integerp i)
     (<= 0 i)
     (< i (len sequence))
     (mapview-eq-p
      (mapview-key (nth i sequence))
      key))))

;; The source view and returned map-view datatypes use exact tagged encodings.

(defun mapview-view-empty ()
  (list :view-empty))

(defun mapview-view-empty-p (view)
  (equal view (mapview-view-empty)))

(defun mapview-view-node-shape-p (view)
  (and
   (true-listp view)
   (equal (len view) 6)
   (equal (car view) :view-node)))

(defun mapview-view-left (view)
  (cadr view))

(defun mapview-view-item (view)
  (caddr view))

(defun mapview-view-right (view)
  (cadddr view))

(defun mapview-view-height (view)
  (car (cddddr view)))

(defun mapview-view-unit (view)
  (cadr (cddddr view)))

(defun mapview-view-p (view)
  (or
   (mapview-view-empty-p view)
   (and
    (mapview-view-node-shape-p view)
    (mapview-tree-object-p (mapview-view-left view))
    (mapview-item-p (mapview-view-item view))
    (mapview-tree-object-p (mapview-view-right view))
    (natp (mapview-view-height view))
    (equal (mapview-view-unit view) :unit))))

(defun mapview-result-empty ()
  (list :result-empty))

(defun mapview-result-empty-p (result)
  (equal result (mapview-result-empty)))

(defun mapview-result-node-shape-p (result)
  (and
   (true-listp result)
   (equal (len result) 5)
   (equal (car result) :result-node)))

(defun mapview-result-left (result)
  (cadr result))

(defun mapview-result-item (result)
  (caddr result))

(defun mapview-result-right (result)
  (cadddr result))

(defun mapview-result-height (result)
  (car (cddddr result)))

(defun mapview-result-p (result)
  (or
   (mapview-result-empty-p result)
   (and
    (mapview-result-node-shape-p result)
    (mapview-map-p (mapview-result-left result))
    (mapview-item-p (mapview-result-item result))
    (mapview-map-p (mapview-result-right result))
    (natp (mapview-result-height result)))))

;; These accessors are the three fields of m3, with its definition unfolded.

(defun mapview-map-sequence (map)
  (mapview-model-sequence
   (mapview-m1
    (mapview-field map))))

(defun mapview-map-domain-p (map key)
  (equal
   (mapview-domain-closure
    (mapview-map-sequence map)
    key)
   t))

(defun mapview-map-function (map key)
  (mapview-make-func-closure
   (mapview-map-sequence map)
   key))

(defun mapview-map-cardinality (map)
  (len (mapview-map-sequence map)))

;; Every ambient source declaration becomes an explicit hypothesis. The item
;; and key carriers remain arbitrary and potentially infinite.

(defun-sk mapview-carriers-inhabited-p ()
  (exists
    (item key t2 selector part tree-object map)
    (and
     (mapview-item-p item)
     (mapview-key-p key)
     (mapview-t2-p t2)
     (mapview-selector-p selector)
     (mapview-part-p part)
     (mapview-tree-object-p tree-object)
     (mapview-map-p map))))

(defun-sk mapview-operation-closures-p ()
  (forall (item key tree-object map sequence)
    (and
     (implies
      (mapview-item-p item)
      (mapview-key-p
       (mapview-key item)))
     (implies
      (mapview-tree-object-p tree-object)
      (and
       (mapview-tree-p
        (mapview-repr tree-object))
       (mapview-model-p
        (mapview-m1 tree-object))))
     (implies
      (mapview-map-p map)
      (mapview-tree-object-p
       (mapview-field map)))
     (implies
      (and
       (mapview-item-list-p sequence)
       (mapview-key-p key))
      (and
       (mapview-item-p
        (mapview-make-func sequence key))
       (booleanp
        (mapview-domain-closure sequence key))
       (mapview-item-p
        (mapview-make-func-closure
         sequence key)))))))

(defun-sk mapview-order-reflexive-p ()
  (forall (key)
    (implies
     (mapview-key-p key)
     (mapview-le-p key key))))

(defun-sk mapview-order-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (mapview-key-p x)
      (mapview-key-p y)
      (mapview-key-p z)
      (mapview-le-p x y)
      (mapview-le-p y z))
     (mapview-le-p x z))))

(defun-sk mapview-order-total-p ()
  (forall (x y)
    (implies
     (and
      (mapview-key-p x)
      (mapview-key-p y))
     (or
      (mapview-le-p x y)
      (mapview-le-p y x)))))

(defun-sk mapview-tree-object-invariant-p ()
  (forall (object)
    (implies
     (mapview-tree-object-p object)
     (let ((tree (mapview-repr object))
           (model (mapview-m1 object)))
       (and
        (mapview-balanced-p tree)
        (equal
         (mapview-model-sequence model)
         (mapview-sequence-model tree))
        (equal
         (mapview-model-height model)
         (mapview-real-height tree)))))))

(defun-sk mapview-tree-object-injective-p ()
  (forall (left right)
    (implies
     (and
      (mapview-tree-object-p left)
      (mapview-tree-object-p right)
      (equal
       (mapview-repr left)
       (mapview-repr right))
      (equal
       (mapview-m1 left)
       (mapview-m1 right)))
     (equal left right))))

(defun-sk mapview-map-invariant-p ()
  (forall (map)
    (implies
     (mapview-map-p map)
     (mapview-selection-possible-p
      (mapview-map-sequence map)))))

(defun-sk mapview-map-injective-p ()
  (forall (left right)
    (implies
     (and
      (mapview-map-p left)
      (mapview-map-p right)
      (equal
       (mapview-field left)
       (mapview-field right)))
     (equal left right))))

(defun-sk mapview-make-func-specification-p ()
  (forall (sequence key i)
    (implies
     (and
      (mapview-item-list-p sequence)
      (mapview-key-p key)
      (integerp i)
      (mapview-selection-possible-p sequence)
      (mapview-domain-p sequence key)
      (<= 0 i)
      (< i (len sequence))
      (mapview-eq-p
       (mapview-key (nth i sequence))
       key))
     (equal
      (mapview-make-func sequence key)
      (nth i sequence)))))

(defun-sk mapview-domain-closure-specification-p ()
  (forall (sequence key)
    (implies
     (and
      (mapview-item-list-p sequence)
      (mapview-key-p key))
     (iff
      (equal
       (mapview-domain-closure sequence key)
       t)
      (mapview-domain-p sequence key)))))

(defun-sk mapview-make-func-closure-specification-p ()
  (forall (sequence key)
    (implies
     (and
      (mapview-item-list-p sequence)
      (mapview-key-p key))
     (equal
      (mapview-make-func-closure sequence key)
      (mapview-make-func sequence key)))))

(defun mapview-background-p ()
  (and
   (natp (mapview-balancing))
   (< 0 (mapview-balancing))
   (mapview-carriers-inhabited-p)
   (mapview-operation-closures-p)
   (mapview-order-reflexive-p)
   (mapview-order-transitive-p)
   (mapview-order-total-p)
   (mapview-tree-object-invariant-p)
   (mapview-tree-object-injective-p)
   (mapview-map-invariant-p)
   (mapview-map-injective-p)
   (mapview-make-func-specification-p)
   (mapview-domain-closure-specification-p)
   (mapview-make-func-closure-specification-p)))

;; This is the source match on the candidate view in the outer premise.

(defun mapview-view-premise-p (original-tree view)
  (let ((original-model (mapview-m1 original-tree)))
    (if (mapview-view-empty-p view)
        (and
         (equal
          (mapview-model-height original-model)
          0)
         (equal
          (mapview-model-sequence original-model)
          nil))
      (let* ((left (mapview-view-left view))
             (item (mapview-view-item view))
             (right (mapview-view-right view))
             (height (mapview-view-height view))
             (left-height
              (mapview-model-height
               (mapview-m1 left)))
             (right-height
              (mapview-model-height
               (mapview-m1 right)))
             (difference
              (- left-height right-height)))
        (and
         (equal
          (mapview-model-sequence original-model)
          (mapview-node-model
           (mapview-model-sequence
            (mapview-m1 left))
           item
           (mapview-model-sequence
            (mapview-m1 right))))
         (equal (mapview-view-unit view) :unit)
         (<= (- (mapview-balancing)) difference)
         (<= difference (mapview-balancing))
         (equal
          (mapview-model-height original-model)
          height)
         (equal
          height
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height))))))))

;; For a node view, the source first requires the right sequence to be sorted
;; and conditionally requires the left sequence to be sorted for every map
;; whose field is the left tree object.

(defun-sk mapview-left-selection-continuation-p (left right)
  (forall (right-map)
    (implies
     (and
      (mapview-map-p right-map)
      (equal
       (mapview-field right-map)
       right))
     (mapview-selection-possible-p
      (mapview-model-sequence
       (mapview-m1 left))))))

(defun mapview-node-selection-conclusion-p (view)
  (if (mapview-view-empty-p view)
      t
    (and
     (mapview-selection-possible-p
      (mapview-model-sequence
       (mapview-m1
        (mapview-view-right view))))
     (mapview-left-selection-continuation-p
      (mapview-view-left view)
      (mapview-view-right view)))))

;; The relation between the input view and returned view retains both internal
;; existential map witnesses from the source statement.

(defun-sk mapview-node-result-related-p
    (left-tree item right-tree height result)
  (exists (right-map left-map)
    (and
     (mapview-map-p right-map)
     (equal
      (mapview-field right-map)
      right-tree)
     (mapview-map-p left-map)
     (equal
      (mapview-field left-map)
      left-tree)
     (equal
      result
      (list
       :result-node
       left-map
       item
       right-map
       height)))))

(defun mapview-result-related-p (view result)
  (if (mapview-view-empty-p view)
      (mapview-result-empty-p result)
    (mapview-node-result-related-p
     (mapview-view-left view)
     (mapview-view-item view)
     (mapview-view-right view)
     (mapview-view-height view)
     result)))

;; Each source universal key clause in the node postcondition is preserved.

(defun-sk mapview-node-key-clauses-p
    (original left item right)
  (forall (key)
    (let ((key0 (mapview-key item)))
      (implies
       (mapview-key-p key)
       (and
        (implies
         (mapview-lt-p key key0)
         (iff
          (mapview-map-domain-p left key)
          (mapview-map-domain-p original key)))
        (implies
         (and
          (mapview-lt-p key key0)
          (mapview-map-domain-p left key))
         (equal
          (mapview-map-function left key)
          (mapview-map-function original key)))
        (implies
         (mapview-le-p key0 key)
         (not
          (mapview-map-domain-p left key)))
        (implies
         (mapview-lt-p key0 key)
         (iff
          (mapview-map-domain-p right key)
          (mapview-map-domain-p original key)))
        (implies
         (and
          (mapview-lt-p key0 key)
          (mapview-map-domain-p right key))
         (equal
          (mapview-map-function right key)
          (mapview-map-function original key)))
        (implies
         (mapview-le-p key key0)
         (not
          (mapview-map-domain-p right key)))
        (implies
         (mapview-eq-p key key0)
         (and
          (mapview-map-domain-p original key)
          (equal
           (mapview-map-function original key)
           item))))))))

(defun-sk mapview-empty-domain-p (map)
  (forall (key)
    (implies
     (mapview-key-p key)
     (not
      (mapview-map-domain-p map key)))))

(defun mapview-result-postcondition-p (original result)
  (if (mapview-result-empty-p result)
      (and
       (equal
        (mapview-map-cardinality original)
        0)
       (mapview-empty-domain-p original))
    (let* ((left (mapview-result-left result))
           (item (mapview-result-item result))
           (right (mapview-result-right result))
           (height (mapview-result-height result))
           (key0 (mapview-key item)))
      (and
       (equal
        (mapview-map-cardinality original)
        (+ 1
           (mapview-map-cardinality left)
           (mapview-map-cardinality right)))
       (equal
        height
        (mapview-model-height
         (mapview-m1
          (mapview-field original))))
       (mapview-node-key-clauses-p
        original left item right)
       (mapview-map-domain-p original key0)
       (equal
        (mapview-map-function original key0)
        item)))))

(defun-sk mapview-all-results-p (original view)
  (forall (result)
    (implies
     (mapview-result-p result)
     (implies
      (mapview-result-related-p view result)
      (mapview-result-postcondition-p
       original result)))))

(defun mapview-view-conclusion-p (original view)
  (and
   (mapview-node-selection-conclusion-p view)
   (mapview-all-results-p original view)))

(defun-sk mapview-all-views-p (original)
  (forall (view)
    (implies
     (mapview-view-p view)
     (implies
      (mapview-view-premise-p
       (mapview-field original)
       view)
      (mapview-view-conclusion-p
       original view)))))

(defun-sk
    ntp4vc-pearl-avl-tables-mapbase-viewqtvc-statement ()
  (forall (original)
    (implies
     (mapview-map-p original)
     (implies
      (mapview-background-p)
      (mapview-all-views-p original)))))

(value-triple :itpeval-statement-checked)
:q
