;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/tables_MapBase_removeqtvc: the AVL-map removal verification
;; condition preserving sorted key order while updating cardinality, domain,
;; and unaffected lookup bindings. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent one fixed arbitrary inhabited
;; source parameter type and its item, key, tree-object, and map carriers.
;; Every source law used below is explicit in the statement context.

(defstub mapremove-item-p (x) t)
(defstub mapremove-key-p (x) t)
(defstub mapremove-key (item) t)
(defstub mapremove-le (left right) t)
(defstub mapremove-balancing () t)

(defstub mapremove-tree-object-p (x) t)
(defstub mapremove-repr (object) t)
(defstub mapremove-model-sequence (object) t)
(defstub mapremove-model-height (object) t)

(defstub mapremove-map-p (x) t)
(defstub mapremove-field (map) t)
(defstub mapremove-make-function (sequence key) t)

;; Source lists are finite, while their item and key carriers remain arbitrary
;; and potentially infinite.

(defun mapremove-item-list-p (sequence)
  (if (consp sequence)
      (and
       (mapremove-item-p (car sequence))
       (mapremove-item-list-p (cdr sequence)))
    (equal sequence nil)))

(defun mapremove-key-eq-p (left right)
  (and
   (mapremove-le left right)
   (mapremove-le right left)))

(defun mapremove-key-lt-p (left right)
  (and
   (mapremove-le left right)
   (not (mapremove-le right left))))

(defun mapremove-nth-item (index sequence)
  (nth (nfix index) sequence))

;; The first source argument of selection_possible is definitionally ignored.

(defun-sk mapremove-selection-possible-p (sequence)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j)
      (<= 0 i)
      (< i j)
      (< j (len sequence)))
     (mapremove-key-lt-p
      (mapremove-key
       (mapremove-nth-item i sequence))
      (mapremove-key
       (mapremove-nth-item j sequence))))))

(defun-sk mapremove-upper-bound-p (key sequence)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len sequence)))
     (mapremove-key-lt-p
      (mapremove-key
       (mapremove-nth-item i sequence))
      key))))

(defun-sk mapremove-lower-bound-p (key sequence)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len sequence)))
     (mapremove-key-lt-p
      key
      (mapremove-key
       (mapremove-nth-item i sequence))))))

;; A split is the source record (left1, middle, right1). NIL represents None,
;; while (:SOME item) represents Some item.

(defun mapremove-option-item-p (option)
  (or
   (equal option nil)
   (and
    (true-listp option)
    (equal (len option) 2)
    (equal (car option) :some)
    (mapremove-item-p (cadr option)))))

(defun mapremove-split-p (split)
  (and
   (true-listp split)
   (equal (len split) 4)
   (equal (car split) :split)
   (mapremove-item-list-p (cadr split))
   (mapremove-option-item-p (caddr split))
   (mapremove-item-list-p (cadddr split))))

(defun mapremove-split-left (split)
  (cadr split))

(defun mapremove-split-middle (split)
  (caddr split))

(defun mapremove-split-right (split)
  (cadddr split))

(defun mapremove-option-to-list (option)
  (if (equal option nil)
      nil
    (list (cadr option))))

(defun mapremove-rebuild (split)
  (append
   (mapremove-split-left split)
   (append
    (mapremove-option-to-list
     (mapremove-split-middle split))
    (mapremove-split-right split))))

(defun mapremove-selected-p (key split)
  (and
   (mapremove-upper-bound-p
    key
    (mapremove-split-left split))
   (mapremove-lower-bound-p
    key
    (mapremove-split-right split))
   (let ((middle (mapremove-split-middle split)))
     (if (equal middle nil)
         t
       (mapremove-key-eq-p
        key
        (mapremove-key (cadr middle)))))))

(defun mapremove-node-model (left item right)
  (append left (cons item right)))

;; Unit is a singleton, so omitting the source node's unit-valued field gives
;; a definitional bijection with :EMPTY and
;; (:NODE left item right stored-height).

(defun mapremove-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 5)
   (equal (car tree) :node)))

(defun mapremove-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (or
   (equal tree :empty)
   (and
    (mapremove-node-shape-p tree)
    (mapremove-tree-p (cadr tree))
    (mapremove-item-p (caddr tree))
    (mapremove-tree-p (cadddr tree))
    (natp (car (cddddr tree))))))

(defun mapremove-tree-left (tree)
  (cadr tree))

(defun mapremove-tree-item (tree)
  (caddr tree))

(defun mapremove-tree-right (tree)
  (cadddr tree))

(defun mapremove-tree-stored-height (tree)
  (car (cddddr tree)))

(defun mapremove-sequence-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (mapremove-node-shape-p tree))
      nil
    (mapremove-node-model
     (mapremove-sequence-model
      (mapremove-tree-left tree))
     (mapremove-tree-item tree)
     (mapremove-sequence-model
      (mapremove-tree-right tree)))))

(defun mapremove-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (mapremove-node-shape-p tree))
      0
    (let ((left-height
           (mapremove-real-height
            (mapremove-tree-left tree)))
          (right-height
           (mapremove-real-height
            (mapremove-tree-right tree))))
      (+ 1
         (if (< left-height right-height)
             right-height
           left-height)))))

(defun mapremove-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (mapremove-node-shape-p tree))
      t
    (let* ((left (mapremove-tree-left tree))
           (right (mapremove-tree-right tree))
           (difference
            (- (mapremove-real-height right)
               (mapremove-real-height left))))
      (and
       (equal
        (mapremove-tree-stored-height tree)
        (mapremove-real-height tree))
       (<= (- (mapremove-balancing)) difference)
       (<= difference (mapremove-balancing))
       (mapremove-balanced-p left)
       (mapremove-balanced-p right)))))

;; The source domain keeps its existential integer index internal.

(defun-sk mapremove-domain-p (sequence key)
  (exists (i)
    (and
     (integerp i)
     (<= 0 i)
     (< i (len sequence))
     (mapremove-key-eq-p
      (mapremove-key
       (mapremove-nth-item i sequence))
      key))))

;; The ambient source declarations become explicit hypotheses. The arbitrary
;; carriers remain potentially infinite.

(defun-sk mapremove-carriers-inhabited-p ()
  (exists (item key tree-object map)
    (and
     (mapremove-item-p item)
     (mapremove-key-p key)
     (mapremove-tree-object-p tree-object)
     (mapremove-map-p map))))

(defun-sk mapremove-key-and-order-laws-p ()
  (forall (item x y z)
    (and
     (implies
      (mapremove-item-p item)
      (mapremove-key-p
       (mapremove-key item)))
     (implies
      (mapremove-key-p x)
      (mapremove-le x x))
     (implies
      (and
       (mapremove-key-p x)
       (mapremove-key-p y)
       (mapremove-key-p z)
       (mapremove-le x y)
       (mapremove-le y z))
      (mapremove-le x z))
     (implies
      (and
       (mapremove-key-p x)
       (mapremove-key-p y))
      (or
       (mapremove-le x y)
       (mapremove-le y x))))))

(defun-sk mapremove-tree-object-laws-p ()
  (forall (self left right)
    (and
     (implies
      (mapremove-tree-object-p self)
      (and
       (mapremove-tree-p
        (mapremove-repr self))
       (mapremove-balanced-p
        (mapremove-repr self))
       (mapremove-item-list-p
        (mapremove-model-sequence self))
       (equal
        (mapremove-model-sequence self)
        (mapremove-sequence-model
         (mapremove-repr self)))
       (integerp
        (mapremove-model-height self))
       (equal
        (mapremove-model-height self)
        (mapremove-real-height
         (mapremove-repr self)))))
     (implies
      (and
       (mapremove-tree-object-p left)
       (mapremove-tree-object-p right)
       (equal
        (mapremove-repr left)
        (mapremove-repr right))
       (equal
        (mapremove-model-sequence left)
        (mapremove-model-sequence right))
       (equal
        (mapremove-model-height left)
        (mapremove-model-height right)))
      (equal left right)))))

(defun-sk mapremove-map-laws-p ()
  (forall (self left right)
    (and
     (implies
      (mapremove-map-p self)
      (and
       (mapremove-tree-object-p
        (mapremove-field self))
       (mapremove-selection-possible-p
        (mapremove-model-sequence
         (mapremove-field self)))))
     (implies
      (and
       (mapremove-map-p left)
       (mapremove-map-p right)
       (equal
        (mapremove-field left)
        (mapremove-field right)))
      (equal left right)))))

(defun-sk mapremove-make-function-laws-p ()
  (forall (sequence key i)
    (and
     (implies
      (and
       (mapremove-item-list-p sequence)
       (mapremove-key-p key))
      (mapremove-item-p
       (mapremove-make-function sequence key)))
     (implies
      (and
       (mapremove-item-list-p sequence)
       (mapremove-key-p key)
       (integerp i)
       (mapremove-selection-possible-p sequence)
       (mapremove-domain-p sequence key)
       (<= 0 i)
       (< i (len sequence))
       (mapremove-key-eq-p
        (mapremove-key
         (mapremove-nth-item i sequence))
        key))
      (equal
       (mapremove-make-function sequence key)
       (mapremove-nth-item i sequence))))))

(defun mapremove-context-p ()
  (and
   (natp (mapremove-balancing))
   (< 0 (mapremove-balancing))
   (mapremove-carriers-inhabited-p)
   (mapremove-key-and-order-laws-p)
   (mapremove-tree-object-laws-p)
   (mapremove-map-laws-p)
   (mapremove-make-function-laws-p)))

;; These are the three fields of the source m3 record, definitionally reduced
;; through domain_closure_def and make_func_closure_def.

(defun mapremove-map-sequence (map)
  (mapremove-model-sequence
   (mapremove-field map)))

(defun mapremove-map-domain-p (map key)
  (mapremove-domain-p
   (mapremove-map-sequence map)
   key))

(defun mapremove-map-function (map key)
  (mapremove-make-function
   (mapremove-map-sequence map)
   key))

(defun mapremove-map-cardinality (map)
  (len (mapremove-map-sequence map)))

(defun-sk mapremove-equivalent-key-absent-p (result removed-key)
  (forall (key)
    (implies
     (and
      (mapremove-key-p key)
      (mapremove-key-eq-p key removed-key))
     (not
      (mapremove-map-domain-p result key)))))

(defun-sk mapremove-other-domains-preserved-p
    (original result removed-key)
  (forall (key)
    (implies
     (and
      (mapremove-key-p key)
      (not
       (mapremove-key-eq-p key removed-key)))
     (iff
      (mapremove-map-domain-p result key)
      (mapremove-map-domain-p original key)))))

(defun-sk mapremove-other-functions-preserved-p
    (original result removed-key)
  (forall (key)
    (implies
     (and
      (mapremove-key-p key)
      (not
       (mapremove-key-eq-p key removed-key))
      (mapremove-map-domain-p result key))
     (equal
      (mapremove-map-function result key)
      (mapremove-map-function original key)))))

(defun-sk mapremove-result-map-postcondition-p
    (original removed-key tree-result)
  (forall (result)
    (implies
     (and
      (mapremove-map-p result)
      (equal
       (mapremove-field result)
       tree-result))
     (and
      (equal
       (mapremove-map-cardinality result)
       (if
        (mapremove-map-domain-p original removed-key)
        (- (mapremove-map-cardinality original) 1)
        (mapremove-map-cardinality original)))
      (mapremove-equivalent-key-absent-p
       result removed-key)
      (not
       (mapremove-map-domain-p result removed-key))
      (mapremove-other-domains-preserved-p
       original result removed-key)
      (mapremove-other-functions-preserved-p
       original result removed-key)))))

(defun-sk mapremove-tree-result-continuation-p
    (original removed-key original-tree)
  (forall (split tree-result)
    (implies
     (and
      (mapremove-split-p split)
      (mapremove-tree-object-p tree-result)
      (equal
       (mapremove-model-sequence tree-result)
       (append
        (mapremove-split-left split)
        (mapremove-split-right split)))
      (mapremove-selected-p removed-key split)
      (equal
       (mapremove-rebuild split)
       (mapremove-model-sequence original-tree))
      (<=
       (- (mapremove-model-height original-tree)
          (mapremove-model-height tree-result))
       1)
      (<=
       0
       (- (mapremove-model-height original-tree)
          (mapremove-model-height tree-result))))
     (and
      (mapremove-selection-possible-p
       (mapremove-model-sequence tree-result))
      (mapremove-result-map-postcondition-p
       original removed-key tree-result)))))

(defun-sk
    ntp4vc-pearl-avl-tables-mapbase-removeqtvc-statement ()
  (forall (original removed-key)
    (implies
     (and
      (mapremove-context-p)
      (mapremove-map-p original)
      (mapremove-key-p removed-key))
     (let ((original-tree
            (mapremove-field original)))
       (and
        (mapremove-selection-possible-p
         (mapremove-model-sequence original-tree))
        (mapremove-tree-result-continuation-p
         original removed-key original-tree))))))

(value-triple :itpeval-statement-checked)
:q
