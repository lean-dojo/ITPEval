;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/tables_MapBase_splitqtvc: the AVL-map split verification
;; condition relating the selected decomposition to sorted left and right
;; maps, their domains, lookup functions, and cardinalities. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent one fixed arbitrary inhabited
;; source parameter type and its item, key, tree-object, and map carriers.
;; Every source law used below is explicit in the statement context.

(defstub mapsplit-item-p (x) t)
(defstub mapsplit-key-p (x) t)
(defstub mapsplit-key (item) t)
(defstub mapsplit-le (left right) t)
(defstub mapsplit-balancing () t)

(defstub mapsplit-tree-object-p (x) t)
(defstub mapsplit-repr (object) t)
(defstub mapsplit-model-sequence (object) t)
(defstub mapsplit-model-height (object) t)

(defstub mapsplit-map-p (x) t)
(defstub mapsplit-field (map) t)
(defstub mapsplit-make-function (sequence key) t)

;; Source lists are finite, while their item and key carriers remain
;; arbitrary and potentially infinite.

(defun mapsplit-item-list-p (sequence)
  (if (consp sequence)
      (and
       (mapsplit-item-p (car sequence))
       (mapsplit-item-list-p (cdr sequence)))
    (equal sequence nil)))

(defun mapsplit-key-eq-p (left right)
  (and
   (mapsplit-le left right)
   (mapsplit-le right left)))

(defun mapsplit-key-lt-p (left right)
  (and
   (mapsplit-le left right)
   (not (mapsplit-le right left))))

(defun mapsplit-nth-item (index sequence)
  (nth (nfix index) sequence))

;; The first source argument of selection_possible is definitionally ignored.

(defun-sk mapsplit-selection-possible-p (sequence)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j)
      (<= 0 i)
      (< i j)
      (< j (len sequence)))
     (mapsplit-key-lt-p
      (mapsplit-key
       (mapsplit-nth-item i sequence))
      (mapsplit-key
       (mapsplit-nth-item j sequence))))))

(defun-sk mapsplit-upper-bound-p (key sequence)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len sequence)))
     (mapsplit-key-lt-p
      (mapsplit-key
       (mapsplit-nth-item i sequence))
      key))))

(defun-sk mapsplit-lower-bound-p (key sequence)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len sequence)))
     (mapsplit-key-lt-p
      key
      (mapsplit-key
       (mapsplit-nth-item i sequence))))))

;; A split is the source record (left1, middle, right1). NIL represents None,
;; while (:SOME item) represents Some item.

(defun mapsplit-option-item-p (option)
  (or
   (equal option nil)
   (and
    (true-listp option)
    (equal (len option) 2)
    (equal (car option) :some)
    (mapsplit-item-p (cadr option)))))

(defun mapsplit-split-p (split)
  (and
   (true-listp split)
   (equal (len split) 4)
   (equal (car split) :split)
   (mapsplit-item-list-p (cadr split))
   (mapsplit-option-item-p (caddr split))
   (mapsplit-item-list-p (cadddr split))))

(defun mapsplit-split-left (split)
  (cadr split))

(defun mapsplit-split-middle (split)
  (caddr split))

(defun mapsplit-split-right (split)
  (cadddr split))

(defun mapsplit-option-to-list (option)
  (if (equal option nil)
      nil
    (list (cadr option))))

(defun mapsplit-rebuild (split)
  (append
   (mapsplit-split-left split)
   (append
    (mapsplit-option-to-list
     (mapsplit-split-middle split))
    (mapsplit-split-right split))))

(defun mapsplit-selected-p (key split)
  (and
   (mapsplit-upper-bound-p
    key
    (mapsplit-split-left split))
   (mapsplit-lower-bound-p
    key
    (mapsplit-split-right split))
   (let ((middle (mapsplit-split-middle split)))
     (if (equal middle nil)
         t
       (mapsplit-key-eq-p
        key
        (mapsplit-key (cadr middle)))))))

(defun mapsplit-node-model (left item right)
  (append left (cons item right)))

;; Unit is a singleton, so omitting the source node's unit-valued field gives
;; a definitional bijection with :EMPTY and
;; (:NODE left item right stored-height).

(defun mapsplit-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 5)
   (equal (car tree) :node)))

(defun mapsplit-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (or
   (equal tree :empty)
   (and
    (mapsplit-node-shape-p tree)
    (mapsplit-tree-p (cadr tree))
    (mapsplit-item-p (caddr tree))
    (mapsplit-tree-p (cadddr tree))
    (natp (car (cddddr tree))))))

(defun mapsplit-tree-left (tree)
  (cadr tree))

(defun mapsplit-tree-item (tree)
  (caddr tree))

(defun mapsplit-tree-right (tree)
  (cadddr tree))

(defun mapsplit-tree-stored-height (tree)
  (car (cddddr tree)))

(defun mapsplit-sequence-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (mapsplit-node-shape-p tree))
      nil
    (mapsplit-node-model
     (mapsplit-sequence-model
      (mapsplit-tree-left tree))
     (mapsplit-tree-item tree)
     (mapsplit-sequence-model
      (mapsplit-tree-right tree)))))

(defun mapsplit-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (mapsplit-node-shape-p tree))
      0
    (let ((left-height
           (mapsplit-real-height
            (mapsplit-tree-left tree)))
          (right-height
           (mapsplit-real-height
            (mapsplit-tree-right tree))))
      (+ 1
         (if (< left-height right-height)
             right-height
           left-height)))))

(defun mapsplit-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (mapsplit-node-shape-p tree))
      t
    (let* ((left (mapsplit-tree-left tree))
           (right (mapsplit-tree-right tree))
           (difference
            (- (mapsplit-real-height right)
               (mapsplit-real-height left))))
      (and
       (equal
        (mapsplit-tree-stored-height tree)
        (mapsplit-real-height tree))
       (<= (- (mapsplit-balancing)) difference)
       (<= difference (mapsplit-balancing))
       (mapsplit-balanced-p left)
       (mapsplit-balanced-p right)))))

;; The source domain keeps its existential integer index internal.

(defun-sk mapsplit-domain-p (sequence key)
  (exists (i)
    (and
     (integerp i)
     (<= 0 i)
     (< i (len sequence))
     (mapsplit-key-eq-p
      (mapsplit-key
       (mapsplit-nth-item i sequence))
      key))))

;; The ambient source declarations become explicit hypotheses. The arbitrary
;; carriers remain potentially infinite.

(defun-sk mapsplit-carriers-inhabited-p ()
  (exists (item key tree-object map)
    (and
     (mapsplit-item-p item)
     (mapsplit-key-p key)
     (mapsplit-tree-object-p tree-object)
     (mapsplit-map-p map))))

(defun-sk mapsplit-key-and-order-laws-p ()
  (forall (item x y z)
    (and
     (implies
      (mapsplit-item-p item)
      (mapsplit-key-p
       (mapsplit-key item)))
     (implies
      (mapsplit-key-p x)
      (mapsplit-le x x))
     (implies
      (and
       (mapsplit-key-p x)
       (mapsplit-key-p y)
       (mapsplit-key-p z)
       (mapsplit-le x y)
       (mapsplit-le y z))
      (mapsplit-le x z))
     (implies
      (and
       (mapsplit-key-p x)
       (mapsplit-key-p y))
      (or
       (mapsplit-le x y)
       (mapsplit-le y x))))))

(defun-sk mapsplit-tree-object-laws-p ()
  (forall (self left right)
    (and
     (implies
      (mapsplit-tree-object-p self)
      (and
       (mapsplit-tree-p
        (mapsplit-repr self))
       (mapsplit-balanced-p
        (mapsplit-repr self))
       (mapsplit-item-list-p
        (mapsplit-model-sequence self))
       (equal
        (mapsplit-model-sequence self)
        (mapsplit-sequence-model
         (mapsplit-repr self)))
       (integerp
        (mapsplit-model-height self))
       (equal
        (mapsplit-model-height self)
        (mapsplit-real-height
         (mapsplit-repr self)))))
     (implies
      (and
       (mapsplit-tree-object-p left)
       (mapsplit-tree-object-p right)
       (equal
        (mapsplit-repr left)
        (mapsplit-repr right))
       (equal
        (mapsplit-model-sequence left)
        (mapsplit-model-sequence right))
       (equal
        (mapsplit-model-height left)
        (mapsplit-model-height right)))
      (equal left right)))))

(defun-sk mapsplit-map-laws-p ()
  (forall (self left right)
    (and
     (implies
      (mapsplit-map-p self)
      (and
       (mapsplit-tree-object-p
        (mapsplit-field self))
       (mapsplit-selection-possible-p
        (mapsplit-model-sequence
         (mapsplit-field self)))))
     (implies
      (and
       (mapsplit-map-p left)
       (mapsplit-map-p right)
       (equal
        (mapsplit-field left)
        (mapsplit-field right)))
      (equal left right)))))

(defun-sk mapsplit-make-function-laws-p ()
  (forall (sequence key i)
    (and
     (implies
      (and
       (mapsplit-item-list-p sequence)
       (mapsplit-key-p key))
      (mapsplit-item-p
       (mapsplit-make-function sequence key)))
     (implies
      (and
       (mapsplit-item-list-p sequence)
       (mapsplit-key-p key)
       (integerp i)
       (mapsplit-selection-possible-p sequence)
       (mapsplit-domain-p sequence key)
       (<= 0 i)
       (< i (len sequence))
       (mapsplit-key-eq-p
        (mapsplit-key
         (mapsplit-nth-item i sequence))
        key))
      (equal
       (mapsplit-make-function sequence key)
       (mapsplit-nth-item i sequence))))))

(defun mapsplit-context-p ()
  (and
   (natp (mapsplit-balancing))
   (< 0 (mapsplit-balancing))
   (mapsplit-carriers-inhabited-p)
   (mapsplit-key-and-order-laws-p)
   (mapsplit-tree-object-laws-p)
   (mapsplit-map-laws-p)
   (mapsplit-make-function-laws-p)))

;; These are the three fields of the source m3 record, definitionally reduced
;; through domain_closure_def and make_func_closure_def.

(defun mapsplit-map-sequence (map)
  (mapsplit-model-sequence
   (mapsplit-field map)))

(defun mapsplit-map-domain-p (map key)
  (mapsplit-domain-p
   (mapsplit-map-sequence map)
   key))

(defun mapsplit-map-function (map key)
  (mapsplit-make-function
   (mapsplit-map-sequence map)
   key))

(defun mapsplit-map-cardinality (map)
  (len (mapsplit-map-sequence map)))

(defun-sk mapsplit-left-selection-continuation-p
    (left-tree right-tree)
  (forall (map)
    (implies
     (and
      (mapsplit-map-p map)
      (equal
       (mapsplit-field map)
       right-tree))
     (mapsplit-selection-possible-p
      (mapsplit-model-sequence left-tree)))))

(defun-sk mapsplit-left-domain-preserved-p
    (original left-map pivot)
  (forall (key)
    (implies
     (and
      (mapsplit-key-p key)
      (mapsplit-key-lt-p key pivot))
     (iff
      (mapsplit-map-domain-p left-map key)
      (mapsplit-map-domain-p original key)))))

(defun-sk mapsplit-left-function-preserved-p
    (original left-map pivot)
  (forall (key)
    (implies
     (and
      (mapsplit-key-p key)
      (mapsplit-key-lt-p key pivot)
      (mapsplit-map-domain-p left-map key))
     (equal
      (mapsplit-map-function left-map key)
      (mapsplit-map-function original key)))))

(defun-sk mapsplit-left-excludes-at-or-above-p
    (left-map pivot)
  (forall (key)
    (implies
     (and
      (mapsplit-key-p key)
      (mapsplit-le pivot key))
     (not
      (mapsplit-map-domain-p left-map key)))))

(defun-sk mapsplit-right-domain-preserved-p
    (original right-map pivot)
  (forall (key)
    (implies
     (and
      (mapsplit-key-p key)
      (mapsplit-key-lt-p pivot key))
     (iff
      (mapsplit-map-domain-p right-map key)
      (mapsplit-map-domain-p original key)))))

(defun-sk mapsplit-right-function-preserved-p
    (original right-map pivot)
  (forall (key)
    (implies
     (and
      (mapsplit-key-p key)
      (mapsplit-key-lt-p pivot key)
      (mapsplit-map-domain-p right-map key))
     (equal
      (mapsplit-map-function right-map key)
      (mapsplit-map-function original key)))))

(defun-sk mapsplit-right-excludes-at-or-below-p
    (right-map pivot)
  (forall (key)
    (implies
     (and
      (mapsplit-key-p key)
      (mapsplit-le key pivot))
     (not
      (mapsplit-map-domain-p right-map key)))))

(defun-sk mapsplit-equivalent-key-absent-p
    (original pivot)
  (forall (key)
    (implies
     (and
      (mapsplit-key-p key)
      (mapsplit-key-eq-p key pivot))
     (not
      (mapsplit-map-domain-p original key)))))

(defun-sk mapsplit-equivalent-key-bound-p
    (original pivot item)
  (forall (key)
    (implies
     (and
      (mapsplit-key-p key)
      (mapsplit-key-eq-p key pivot))
     (and
      (mapsplit-map-domain-p original key)
      (equal
       (mapsplit-map-function original key)
       item)))))

(defun mapsplit-middle-postcondition-p
    (original left-map right-map option pivot)
  (if (equal option nil)
      (and
       (equal
        (mapsplit-map-cardinality original)
        (+ (mapsplit-map-cardinality left-map)
           (mapsplit-map-cardinality right-map)))
       (mapsplit-equivalent-key-absent-p
        original pivot)
       (not
        (mapsplit-map-domain-p original pivot)))
    (let ((item (cadr option)))
      (and
       (equal
        (mapsplit-map-cardinality original)
        (+ 1
           (mapsplit-map-cardinality left-map)
           (mapsplit-map-cardinality right-map)))
       (mapsplit-key-eq-p
        (mapsplit-key item)
        pivot)
       (mapsplit-equivalent-key-bound-p
        original pivot item)
       (mapsplit-map-domain-p original pivot)
       (equal
        (mapsplit-map-function original pivot)
        item)))))

(defun mapsplit-map-pair-postcondition-p
    (original left-map right-map option pivot)
  (and
   (mapsplit-left-domain-preserved-p
    original left-map pivot)
   (mapsplit-left-function-preserved-p
    original left-map pivot)
   (mapsplit-left-excludes-at-or-above-p
    left-map pivot)
   (mapsplit-right-domain-preserved-p
    original right-map pivot)
   (mapsplit-right-function-preserved-p
    original right-map pivot)
   (mapsplit-right-excludes-at-or-below-p
    right-map pivot)
   (mapsplit-middle-postcondition-p
    original left-map right-map option pivot)))

(defun-sk mapsplit-all-map-pairs-p
    (original left-tree right-tree option pivot)
  (forall (left-map right-map)
    (implies
     (and
      (mapsplit-map-p left-map)
      (mapsplit-map-p right-map)
      (equal
       (mapsplit-field right-map)
       right-tree)
      (equal
       (mapsplit-field left-map)
       left-tree))
     (mapsplit-map-pair-postcondition-p
      original left-map right-map option pivot))))

(defun mapsplit-decomposition-conclusion-p
    (original left-tree option right-tree pivot)
  (and
   (mapsplit-selection-possible-p
    (mapsplit-model-sequence right-tree))
   (mapsplit-left-selection-continuation-p
    left-tree right-tree)
   (mapsplit-all-map-pairs-p
    original left-tree right-tree option pivot)))

(defun-sk mapsplit-all-decompositions-p
    (original original-tree pivot)
  (forall (split left-tree option right-tree)
    (implies
     (and
      (mapsplit-split-p split)
      (mapsplit-tree-object-p left-tree)
      (mapsplit-option-item-p option)
      (mapsplit-tree-object-p right-tree)
      (mapsplit-selected-p pivot split)
      (equal
       (mapsplit-rebuild split)
       (mapsplit-model-sequence original-tree))
      (equal
       (mapsplit-model-sequence left-tree)
       (mapsplit-split-left split))
      (equal
       (mapsplit-model-sequence right-tree)
       (mapsplit-split-right split))
      (equal
       (mapsplit-split-middle split)
       option))
     (mapsplit-decomposition-conclusion-p
      original left-tree option right-tree pivot))))

(defun-sk
    ntp4vc-pearl-avl-tables-mapbase-splitqtvc-statement ()
  (forall (original pivot)
    (implies
     (and
      (mapsplit-context-p)
      (mapsplit-map-p original)
      (mapsplit-key-p pivot))
     (let ((original-tree
            (mapsplit-field original)))
       (and
        (mapsplit-selection-possible-p
         (mapsplit-model-sequence original-tree))
        (mapsplit-all-decompositions-p
         original original-tree pivot))))))

(value-triple :itpeval-statement-checked)
:q
