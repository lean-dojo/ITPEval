;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/tables_MapBase_getqtvc: the sorted sequence-map lookup
;; verification condition relating a selected split to map membership,
;; cardinality, and the returned element. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent one fixed arbitrary inhabited source
;; parameter type, the corresponding item and key carriers, the abstract
;; tree and map carriers, and all source operations on those carriers.

(defstub mapbase-item-p (x) t)
(defstub mapbase-key-p (x) t)
(defstub mapbase-t2-p (x) t)
(defstub mapbase-selector-p (x) t)
(defstub mapbase-part-p (x) t)
(defstub mapbase-tree-object-p (x) t)
(defstub mapbase-map-p (x) t)

(defstub mapbase-balancing () t)
(defstub mapbase-key (item) t)
(defstub mapbase-le-op (left right) t)
(defstub mapbase-repr (object) t)
(defstub mapbase-m1 (object) t)
(defstub mapbase-field (map) t)
(defstub mapbase-make-func (sequence key) t)
(defstub mapbase-domain-closure (sequence key) t)
(defstub mapbase-make-func-closure (sequence key) t)

(defun mapbase-le-p (left right)
  (if (mapbase-le-op left right) t nil))

(defun mapbase-eq-p (left right)
  (and
   (mapbase-le-p left right)
   (mapbase-le-p right left)))

(defun mapbase-lt-p (left right)
  (and
   (mapbase-le-p left right)
   (not (mapbase-le-p right left))))

(defun mapbase-item-list-p (sequence)
  (if (endp sequence)
      (equal sequence nil)
    (and
     (mapbase-item-p (car sequence))
     (mapbase-item-list-p (cdr sequence)))))

;; Options and splits are exact tagged representations of the source
;; datatypes Option (t alpha) and split (t alpha).

(defun mapbase-none ()
  (list :none))

(defun mapbase-some (item)
  (list :some item))

(defun mapbase-none-p (option)
  (equal option (mapbase-none)))

(defun mapbase-some-p (option)
  (and
   (true-listp option)
   (equal (len option) 2)
   (equal (car option) :some)
   (mapbase-item-p (cadr option))))

(defun mapbase-option-p (option)
  (or
   (mapbase-none-p option)
   (mapbase-some-p option)))

(defun mapbase-option-value (option)
  (cadr option))

(defun mapbase-option-to-sequence (option)
  (if (mapbase-none-p option)
      nil
    (list (mapbase-option-value option))))

(defun mapbase-split (left middle right)
  (list :split left middle right))

(defun mapbase-split-p (split)
  (and
   (true-listp split)
   (equal (len split) 4)
   (equal (car split) :split)
   (mapbase-item-list-p (cadr split))
   (mapbase-option-p (caddr split))
   (mapbase-item-list-p (cadddr split))))

(defun mapbase-split-left (split)
  (cadr split))

(defun mapbase-split-middle (split)
  (caddr split))

(defun mapbase-split-right (split)
  (cadddr split))

(defun mapbase-rebuild (split)
  (append
   (append
    (mapbase-split-left split)
    (mapbase-option-to-sequence
     (mapbase-split-middle split)))
   (mapbase-split-right split)))

;; The bounded integer-index quantifiers are retained explicitly.  Bounds
;; ensure that ACL2 NTH denotes the same source list element.

(defun-sk mapbase-selection-possible-p (ignored sequence)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j)
      (<= 0 i)
      (< i j)
      (< j (len sequence)))
     (mapbase-lt-p
      (mapbase-key (nth i sequence))
      (mapbase-key (nth j sequence))))))

(defun-sk mapbase-upper-bound-p (key sequence)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len sequence)))
     (mapbase-lt-p
      (mapbase-key (nth i sequence))
      key))))

(defun-sk mapbase-lower-bound-p (key sequence)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len sequence)))
     (mapbase-lt-p
      key
      (mapbase-key (nth i sequence))))))

(defun mapbase-selected-p (key split)
  (and
   (mapbase-upper-bound-p
    key
    (mapbase-split-left split))
   (mapbase-lower-bound-p
    key
    (mapbase-split-right split))
   (or
    (mapbase-none-p
     (mapbase-split-middle split))
    (and
     (mapbase-some-p
      (mapbase-split-middle split))
     (mapbase-eq-p
      key
      (mapbase-key
       (mapbase-option-value
        (mapbase-split-middle split))))))))

;; The source tree datatype is represented by NIL for Empty and exact tagged
;; node records (:TREE-NODE left item right height unit).

(defun mapbase-tree-empty-p (tree)
  (equal tree nil))

(defun mapbase-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun mapbase-tree-left (tree)
  (cadr tree))

(defun mapbase-tree-item (tree)
  (caddr tree))

(defun mapbase-tree-right (tree)
  (cadddr tree))

(defun mapbase-tree-height (tree)
  (car (cddddr tree)))

(defun mapbase-tree-unit (tree)
  (cadr (cddddr tree)))

(defun mapbase-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (mapbase-tree-empty-p tree)
      t
    (and
     (mapbase-tree-node-shape-p tree)
     (mapbase-tree-p (mapbase-tree-left tree))
     (mapbase-item-p (mapbase-tree-item tree))
     (mapbase-tree-p (mapbase-tree-right tree))
     (natp (mapbase-tree-height tree))
     (equal (mapbase-tree-unit tree) :unit))))

;; The source model record m is (:M sequence integer-height).

(defun mapbase-model-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (mapbase-item-list-p (cadr model))
   (integerp (caddr model))))

(defun mapbase-model-sequence (model)
  (cadr model))

(defun mapbase-model-height (model)
  (caddr model))

(defun mapbase-node-model (left item right)
  (append left (cons item right)))

(defun mapbase-sequence-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (mapbase-tree-empty-p tree)
      nil
    (if (mapbase-tree-node-shape-p tree)
        (mapbase-node-model
         (mapbase-sequence-model
          (mapbase-tree-left tree))
         (mapbase-tree-item tree)
         (mapbase-sequence-model
          (mapbase-tree-right tree)))
      nil)))

(defun mapbase-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (mapbase-tree-empty-p tree)
      0
    (if (mapbase-tree-node-shape-p tree)
        (let ((left-height
               (mapbase-real-height
                (mapbase-tree-left tree)))
              (right-height
               (mapbase-real-height
                (mapbase-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun mapbase-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (mapbase-tree-empty-p tree)
      t
    (if (mapbase-tree-node-shape-p tree)
        (let* ((left (mapbase-tree-left tree))
               (right (mapbase-tree-right tree))
               (difference
                (- (mapbase-real-height right)
                   (mapbase-real-height left))))
          (and
           (equal
            (mapbase-tree-height tree)
            (mapbase-real-height tree))
           (equal (mapbase-tree-unit tree) :unit)
           (<= (- (mapbase-balancing)) difference)
           (<= difference (mapbase-balancing))
           (mapbase-balanced-p left)
           (mapbase-balanced-p right)))
      nil)))

;; Domain is the source internal existential over an integer list index.

(defun-sk mapbase-domain-p (sequence key)
  (exists (i)
    (and
     (integerp i)
     (<= 0 i)
     (< i (len sequence))
     (mapbase-eq-p
      (mapbase-key (nth i sequence))
      key))))

;; The concrete m3 value records the source sequence.  Its three accessors
;; are definitionally the two closure functions and the integer list length.

(defun mapbase-m3 (map)
  (list
   :m2
   (mapbase-model-sequence
    (mapbase-m1
     (mapbase-field map)))))

(defun mapbase-m3-p (record)
  (and
   (true-listp record)
   (equal (len record) 2)
   (equal (car record) :m2)
   (mapbase-item-list-p (cadr record))))

(defun mapbase-m3-sequence (record)
  (cadr record))

(defun mapbase-m3-domain (record key)
  (mapbase-domain-closure
   (mapbase-m3-sequence record)
   key))

(defun mapbase-m3-function (record key)
  (mapbase-make-func-closure
   (mapbase-m3-sequence record)
   key))

(defun mapbase-m3-cardinality (record)
  (len (mapbase-m3-sequence record)))

;; Every source carrier, operation closure, order law, representation
;; invariant, injectivity property, and closure specification is an explicit
;; assumption of the statement predicate.

(defun-sk mapbase-carriers-inhabited-p ()
  (exists
    (item key t2 selector part tree-object map)
    (and
     (mapbase-item-p item)
     (mapbase-key-p key)
     (mapbase-t2-p t2)
     (mapbase-selector-p selector)
     (mapbase-part-p part)
     (mapbase-tree-object-p tree-object)
     (mapbase-map-p map))))

(defun-sk mapbase-operation-closures-p ()
  (forall (item key tree-object map sequence)
    (and
     (implies
      (mapbase-item-p item)
      (mapbase-key-p
       (mapbase-key item)))
     (implies
      (mapbase-tree-object-p tree-object)
      (and
       (mapbase-tree-p
        (mapbase-repr tree-object))
       (mapbase-model-p
        (mapbase-m1 tree-object))))
     (implies
      (mapbase-map-p map)
      (mapbase-tree-object-p
       (mapbase-field map)))
     (implies
      (and
       (mapbase-item-list-p sequence)
       (mapbase-key-p key))
      (and
       (mapbase-item-p
        (mapbase-make-func sequence key))
       (booleanp
        (mapbase-domain-closure sequence key))
       (mapbase-item-p
        (mapbase-make-func-closure
         sequence key)))))))

(defun-sk mapbase-order-reflexive-p ()
  (forall (key)
    (implies
     (mapbase-key-p key)
     (mapbase-le-p key key))))

(defun-sk mapbase-order-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (mapbase-key-p x)
      (mapbase-key-p y)
      (mapbase-key-p z)
      (mapbase-le-p x y)
      (mapbase-le-p y z))
     (mapbase-le-p x z))))

(defun-sk mapbase-order-total-p ()
  (forall (x y)
    (implies
     (and
      (mapbase-key-p x)
      (mapbase-key-p y))
     (or
      (mapbase-le-p x y)
      (mapbase-le-p y x)))))

(defun-sk mapbase-tree-object-invariant-p ()
  (forall (object)
    (implies
     (mapbase-tree-object-p object)
     (let ((tree (mapbase-repr object))
           (model (mapbase-m1 object)))
       (and
        (mapbase-balanced-p tree)
        (equal
         (mapbase-model-sequence model)
         (mapbase-sequence-model tree))
        (equal
         (mapbase-model-height model)
         (mapbase-real-height tree)))))))

(defun-sk mapbase-tree-object-injective-p ()
  (forall (left right)
    (implies
     (and
      (mapbase-tree-object-p left)
      (mapbase-tree-object-p right)
      (equal
       (mapbase-repr left)
       (mapbase-repr right))
      (equal
       (mapbase-m1 left)
       (mapbase-m1 right)))
     (equal left right))))

(defun-sk mapbase-map-invariant-p ()
  (forall (map)
    (implies
     (mapbase-map-p map)
     (mapbase-selection-possible-p
      :unit
      (mapbase-model-sequence
       (mapbase-m1
        (mapbase-field map)))))))

(defun-sk mapbase-map-injective-p ()
  (forall (left right)
    (implies
     (and
      (mapbase-map-p left)
      (mapbase-map-p right)
      (equal
       (mapbase-field left)
       (mapbase-field right)))
     (equal left right))))

(defun-sk mapbase-make-func-specification-p ()
  (forall (sequence key i)
    (implies
     (and
      (mapbase-item-list-p sequence)
      (mapbase-key-p key)
      (integerp i)
      (mapbase-selection-possible-p
       :unit sequence)
      (mapbase-domain-p sequence key)
      (<= 0 i)
      (< i (len sequence))
      (mapbase-eq-p
       (mapbase-key (nth i sequence))
       key))
     (equal
      (mapbase-make-func sequence key)
      (nth i sequence)))))

(defun-sk mapbase-domain-closure-specification-p ()
  (forall (sequence key)
    (implies
     (and
      (mapbase-item-list-p sequence)
      (mapbase-key-p key))
     (iff
      (equal
       (mapbase-domain-closure sequence key)
       t)
      (mapbase-domain-p sequence key)))))

(defun-sk mapbase-make-func-closure-specification-p ()
  (forall (sequence key)
    (implies
     (and
      (mapbase-item-list-p sequence)
      (mapbase-key-p key))
     (equal
      (mapbase-make-func-closure sequence key)
      (mapbase-make-func sequence key)))))

(defun mapbase-background-p ()
  (and
   (natp (mapbase-balancing))
   (< 0 (mapbase-balancing))
   (mapbase-carriers-inhabited-p)
   (mapbase-operation-closures-p)
   (mapbase-order-reflexive-p)
   (mapbase-order-transitive-p)
   (mapbase-order-total-p)
   (mapbase-tree-object-invariant-p)
   (mapbase-tree-object-injective-p)
   (mapbase-map-invariant-p)
   (mapbase-map-injective-p)
   (mapbase-make-func-specification-p)
   (mapbase-domain-closure-specification-p)
   (mapbase-make-func-closure-specification-p)))

;; The result-to-middle relation is the source Option match in the premise.

(defun mapbase-result-matches-middle-p (result split)
  (if (mapbase-none-p result)
      (mapbase-none-p
       (mapbase-split-middle split))
    (equal
     (mapbase-split-middle split)
     result)))

(defun mapbase-result-conclusion-p (result map key)
  (let ((record (mapbase-m3 map)))
    (if (mapbase-none-p result)
        (not
         (equal
          (mapbase-m3-domain record key)
          t))
      (let ((item (mapbase-option-value result)))
        (and
         (< 0
            (mapbase-m3-cardinality record))
         (mapbase-eq-p
          (mapbase-key item)
          key)
         (equal
          (mapbase-m3-domain record key)
          t)
         (equal
          (mapbase-m3-function record key)
          item))))))

(defun-sk mapbase-all-lookup-results-p (map key sequence)
  (forall (split result)
    (implies
     (and
      (mapbase-split-p split)
      (mapbase-option-p result))
     (implies
      (and
       (mapbase-selected-p key split)
       (equal
        (mapbase-rebuild split)
        sequence)
       (mapbase-result-matches-middle-p
        result split))
      (mapbase-result-conclusion-p
       result map key)))))

(defun mapbase-get-conclusion-p (map key)
  (let ((sequence
         (mapbase-model-sequence
          (mapbase-m1
           (mapbase-field map)))))
    (and
     (mapbase-selection-possible-p
      key sequence)
     (mapbase-all-lookup-results-p
      map key sequence))))

(defun-sk ntp4vc-pearl-avl-tables-mapbase-getqtvc-statement ()
  (forall (map key)
    (implies
     (and
      (mapbase-map-p map)
      (mapbase-key-p key))
     (implies
      (mapbase-background-p)
      (mapbase-get-conclusion-p
       map key)))))

(value-triple :itpeval-statement-checked)
:q
