;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/tables_MapBase_insertqtvc: the AVL-map insertion verification
;; condition preserving key order and updating the abstract map's cardinality,
;; domain, and lookup function. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The DEFSTUB symbols are the source's arbitrary typed operations.  Their
;; carrier, closure, order, representation, invariant, and lookup laws are all
;; explicit in the statement context below; DEFSTUB itself supplies no law.

(defstub ntp4vc-avl-data-p (x) t)
(defstub ntp4vc-avl-key-p (x) t)
(defstub ntp4vc-avl-key (datum) t)
(defstub ntp4vc-avl-le (left right) t)

(defstub ntp4vc-avl-balancing () t)

(defstub ntp4vc-avl-t3-p (x) t)
(defstub ntp4vc-avl-repr (x) t)
(defstub ntp4vc-avl-model-seq (x) t)
(defstub ntp4vc-avl-model-hgt (x) t)

(defstub ntp4vc-avl-t4-p (x) t)
(defstub ntp4vc-avl-field (x) t)

(defstub ntp4vc-avl-make-func (sequence key) t)

;; Source lists are finite, but their element and key carriers remain arbitrary
;; and potentially infinite.

(defun ntp4vc-avl-data-list-p (xs)
  (if (consp xs)
      (and
       (ntp4vc-avl-data-p (car xs))
       (ntp4vc-avl-data-list-p (cdr xs)))
    (equal xs nil)))

(defun ntp4vc-avl-key-eq (left right)
  (and
   (ntp4vc-avl-le left right)
   (ntp4vc-avl-le right left)))

(defun ntp4vc-avl-key-lt (left right)
  (and
   (ntp4vc-avl-le left right)
   (not (ntp4vc-avl-le right left))))

(defun ntp4vc-avl-nth-data (index sequence)
  (nth (nfix index) sequence))

(defun-sk ntp4vc-avl-selection-possible-p (sequence)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j)
      (<= 0 i)
      (< i j)
      (< j (len sequence)))
     (ntp4vc-avl-key-lt
      (ntp4vc-avl-key
       (ntp4vc-avl-nth-data i sequence))
      (ntp4vc-avl-key
       (ntp4vc-avl-nth-data j sequence))))))

(defun-sk ntp4vc-avl-upper-bound-p (key sequence)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len sequence)))
     (ntp4vc-avl-key-lt
      (ntp4vc-avl-key
       (ntp4vc-avl-nth-data i sequence))
      key))))

(defun-sk ntp4vc-avl-lower-bound-p (key sequence)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len sequence)))
     (ntp4vc-avl-key-lt
      key
      (ntp4vc-avl-key
       (ntp4vc-avl-nth-data i sequence))))))

;; A split is the source record (left1, middle, right1).  NIL is None and
;; (:some datum) is Some datum.

(defun ntp4vc-avl-option-data-p (option)
  (or
   (equal option nil)
   (and
    (true-listp option)
    (equal (len option) 2)
    (equal (car option) :some)
    (ntp4vc-avl-data-p (cadr option)))))

(defun ntp4vc-avl-split-p (split)
  (and
   (true-listp split)
   (equal (len split) 4)
   (equal (car split) :split)
   (ntp4vc-avl-data-list-p (cadr split))
   (ntp4vc-avl-option-data-p (caddr split))
   (ntp4vc-avl-data-list-p (cadddr split))))

(defun ntp4vc-avl-split-left (split)
  (cadr split))

(defun ntp4vc-avl-split-middle (split)
  (caddr split))

(defun ntp4vc-avl-split-right (split)
  (cadddr split))

(defun ntp4vc-avl-option-to-list (option)
  (if (equal option nil)
      nil
    (list (cadr option))))

(defun ntp4vc-avl-rebuild (split)
  (append
   (ntp4vc-avl-split-left split)
   (append
    (ntp4vc-avl-option-to-list
     (ntp4vc-avl-split-middle split))
    (ntp4vc-avl-split-right split))))

(defun ntp4vc-avl-selected-p (key split)
  (and
   (ntp4vc-avl-upper-bound-p
    key (ntp4vc-avl-split-left split))
   (ntp4vc-avl-lower-bound-p
    key (ntp4vc-avl-split-right split))
   (let ((middle (ntp4vc-avl-split-middle split)))
     (if (equal middle nil)
         t
       (ntp4vc-avl-key-eq
        key
        (ntp4vc-avl-key (cadr middle)))))))

(defun ntp4vc-avl-node-model (left datum right)
  (append left (cons datum right)))

;; The source inductive tree is represented without its unit-valued field:
;; :empty or (:node left datum right stored-height).

(defun ntp4vc-avl-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 5)
   (equal (car tree) :node)))

(defun ntp4vc-avl-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (or
   (equal tree :empty)
   (and
    (ntp4vc-avl-node-shape-p tree)
    (ntp4vc-avl-tree-p (cadr tree))
    (ntp4vc-avl-data-p (caddr tree))
    (ntp4vc-avl-tree-p (cadddr tree))
    (natp (car (cddddr tree))))))

(defun ntp4vc-avl-tree-left (tree)
  (cadr tree))

(defun ntp4vc-avl-tree-datum (tree)
  (caddr tree))

(defun ntp4vc-avl-tree-right (tree)
  (cadddr tree))

(defun ntp4vc-avl-tree-stored-height (tree)
  (car (cddddr tree)))

(defun ntp4vc-avl-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (ntp4vc-avl-node-shape-p tree))
      nil
    (ntp4vc-avl-node-model
     (ntp4vc-avl-seq-model
      (ntp4vc-avl-tree-left tree))
     (ntp4vc-avl-tree-datum tree)
     (ntp4vc-avl-seq-model
      (ntp4vc-avl-tree-right tree)))))

(defun ntp4vc-avl-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (ntp4vc-avl-node-shape-p tree))
      0
    (let ((left-height
           (ntp4vc-avl-real-height
            (ntp4vc-avl-tree-left tree)))
          (right-height
           (ntp4vc-avl-real-height
            (ntp4vc-avl-tree-right tree))))
      (+ 1
         (if (< left-height right-height)
             right-height
           left-height)))))

(defun ntp4vc-avl-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (not (ntp4vc-avl-node-shape-p tree))
      t
    (let* ((left (ntp4vc-avl-tree-left tree))
           (right (ntp4vc-avl-tree-right tree))
           (difference
            (- (ntp4vc-avl-real-height right)
               (ntp4vc-avl-real-height left))))
      (and
       (equal
        (ntp4vc-avl-tree-stored-height tree)
        (ntp4vc-avl-real-height tree))
       (<= (- (ntp4vc-avl-balancing)) difference)
       (<= difference (ntp4vc-avl-balancing))
       (ntp4vc-avl-balanced-p left)
       (ntp4vc-avl-balanced-p right)))))

;; The next predicates reproduce the source axioms as explicit hypotheses.

(defun-sk ntp4vc-avl-nonempty-types-p ()
  (exists (datum key tree-map map)
    (and
     (ntp4vc-avl-data-p datum)
     (ntp4vc-avl-key-p key)
     (ntp4vc-avl-t3-p tree-map)
     (ntp4vc-avl-t4-p map))))

(defun-sk ntp4vc-avl-key-and-order-laws-p ()
  (forall (datum x y z)
    (and
     (implies
      (ntp4vc-avl-data-p datum)
      (ntp4vc-avl-key-p
       (ntp4vc-avl-key datum)))
     (implies
      (ntp4vc-avl-key-p x)
      (ntp4vc-avl-le x x))
     (implies
      (and
       (ntp4vc-avl-key-p x)
       (ntp4vc-avl-key-p y)
       (ntp4vc-avl-key-p z)
       (ntp4vc-avl-le x y)
       (ntp4vc-avl-le y z))
      (ntp4vc-avl-le x z))
     (implies
      (and
       (ntp4vc-avl-key-p x)
       (ntp4vc-avl-key-p y))
      (or
       (ntp4vc-avl-le x y)
       (ntp4vc-avl-le y x))))))

(defun-sk ntp4vc-avl-t3-laws-p ()
  (forall (self left right)
    (and
     (implies
      (ntp4vc-avl-t3-p self)
      (and
       (ntp4vc-avl-tree-p
        (ntp4vc-avl-repr self))
       (ntp4vc-avl-balanced-p
        (ntp4vc-avl-repr self))
       (ntp4vc-avl-data-list-p
        (ntp4vc-avl-model-seq self))
       (equal
        (ntp4vc-avl-model-seq self)
        (ntp4vc-avl-seq-model
         (ntp4vc-avl-repr self)))
       (integerp
        (ntp4vc-avl-model-hgt self))
       (equal
        (ntp4vc-avl-model-hgt self)
        (ntp4vc-avl-real-height
         (ntp4vc-avl-repr self)))))
     (implies
      (and
       (ntp4vc-avl-t3-p left)
       (ntp4vc-avl-t3-p right)
       (equal
        (ntp4vc-avl-repr left)
        (ntp4vc-avl-repr right))
       (equal
        (ntp4vc-avl-model-seq left)
        (ntp4vc-avl-model-seq right))
       (equal
        (ntp4vc-avl-model-hgt left)
        (ntp4vc-avl-model-hgt right)))
      (equal left right)))))

(defun-sk ntp4vc-avl-t4-laws-p ()
  (forall (self left right)
    (and
     (implies
      (ntp4vc-avl-t4-p self)
      (and
       (ntp4vc-avl-t3-p
        (ntp4vc-avl-field self))
       (ntp4vc-avl-selection-possible-p
        (ntp4vc-avl-model-seq
         (ntp4vc-avl-field self)))))
     (implies
      (and
       (ntp4vc-avl-t4-p left)
       (ntp4vc-avl-t4-p right)
       (equal
        (ntp4vc-avl-field left)
        (ntp4vc-avl-field right)))
      (equal left right)))))

(defun-sk ntp4vc-avl-domain-p (sequence key)
  (exists (i)
    (and
     (integerp i)
     (<= 0 i)
     (< i (len sequence))
     (ntp4vc-avl-key-eq
      (ntp4vc-avl-key
       (ntp4vc-avl-nth-data i sequence))
      key))))

(defun-sk ntp4vc-avl-make-func-laws-p ()
  (forall (sequence key i)
    (and
     (implies
      (and
       (ntp4vc-avl-data-list-p sequence)
       (ntp4vc-avl-key-p key))
      (ntp4vc-avl-data-p
       (ntp4vc-avl-make-func sequence key)))
     (implies
      (and
       (ntp4vc-avl-data-list-p sequence)
       (ntp4vc-avl-key-p key)
       (integerp i)
       (ntp4vc-avl-selection-possible-p sequence)
       (ntp4vc-avl-domain-p sequence key)
       (<= 0 i)
       (< i (len sequence))
       (ntp4vc-avl-key-eq
        (ntp4vc-avl-key
         (ntp4vc-avl-nth-data i sequence))
        key))
      (equal
       (ntp4vc-avl-make-func sequence key)
       (ntp4vc-avl-nth-data i sequence))))))

(defun ntp4vc-avl-context-p ()
  (and
   (natp (ntp4vc-avl-balancing))
   (< 0 (ntp4vc-avl-balancing))
   (ntp4vc-avl-nonempty-types-p)
   (ntp4vc-avl-key-and-order-laws-p)
   (ntp4vc-avl-t3-laws-p)
   (ntp4vc-avl-t4-laws-p)
   (ntp4vc-avl-make-func-laws-p)))

;; These are the three fields of the source m3 model, definitionally reduced
;; through domain_closure_def and make_func_closure_def.

(defun ntp4vc-avl-map-sequence (map)
  (ntp4vc-avl-model-seq
   (ntp4vc-avl-field map)))

(defun ntp4vc-avl-map-domain-p (map key)
  (ntp4vc-avl-domain-p
   (ntp4vc-avl-map-sequence map)
   key))

(defun ntp4vc-avl-map-func (map key)
  (ntp4vc-avl-make-func
   (ntp4vc-avl-map-sequence map)
   key))

(defun ntp4vc-avl-map-card (map)
  (len (ntp4vc-avl-map-sequence map)))

(defun-sk ntp4vc-avl-inserted-equivalence-p
    (result datum datum-key)
  (forall (key)
    (implies
     (and
      (ntp4vc-avl-key-p key)
      (ntp4vc-avl-key-eq key datum-key))
     (and
      (ntp4vc-avl-map-domain-p result key)
      (equal
       (ntp4vc-avl-map-func result key)
       datum)))))

(defun-sk ntp4vc-avl-other-domain-p
    (original result datum-key)
  (forall (key)
    (implies
     (and
      (ntp4vc-avl-key-p key)
      (not
       (ntp4vc-avl-key-eq key datum-key)))
     (iff
      (ntp4vc-avl-map-domain-p result key)
      (ntp4vc-avl-map-domain-p original key)))))

(defun-sk ntp4vc-avl-other-function-p
    (original result datum-key)
  (forall (key)
    (implies
     (and
      (ntp4vc-avl-key-p key)
      (not
       (ntp4vc-avl-key-eq key datum-key))
      (ntp4vc-avl-map-domain-p result key))
     (equal
     (ntp4vc-avl-map-func result key)
      (ntp4vc-avl-map-func original key)))))

(defun-sk ntp4vc-avl-result-map-postcondition-p
    (original datum tree-result)
  (forall (result)
    (implies
     (and
      (ntp4vc-avl-t4-p result)
      (equal
       (ntp4vc-avl-field result)
       tree-result))
     (let ((datum-key (ntp4vc-avl-key datum)))
       (and
        (equal
         (ntp4vc-avl-map-card result)
         (if
          (ntp4vc-avl-map-domain-p original datum-key)
          (ntp4vc-avl-map-card original)
          (+ 1 (ntp4vc-avl-map-card original))))
        (ntp4vc-avl-inserted-equivalence-p
         result datum datum-key)
        (ntp4vc-avl-map-domain-p result datum-key)
        (equal
         (ntp4vc-avl-map-func result datum-key)
         datum)
        (ntp4vc-avl-other-domain-p
         original result datum-key)
        (ntp4vc-avl-other-function-p
         original result datum-key))))))

(defun-sk ntp4vc-avl-tree-result-continuation-p
    (original datum original-tree datum-key)
  (forall (split tree-result)
    (implies
     (and
      (ntp4vc-avl-split-p split)
      (ntp4vc-avl-t3-p tree-result)
      (equal
       (ntp4vc-avl-model-seq tree-result)
       (ntp4vc-avl-node-model
        (ntp4vc-avl-split-left split)
        datum
        (ntp4vc-avl-split-right split)))
      (ntp4vc-avl-selected-p datum-key split)
      (equal
       (ntp4vc-avl-rebuild split)
       (ntp4vc-avl-model-seq original-tree))
      (<=
       (- (ntp4vc-avl-model-hgt tree-result)
          (ntp4vc-avl-model-hgt original-tree))
       1)
      (<=
       0
       (- (ntp4vc-avl-model-hgt tree-result)
          (ntp4vc-avl-model-hgt original-tree))))
     (and
      (ntp4vc-avl-selection-possible-p
       (ntp4vc-avl-model-seq tree-result))
      (ntp4vc-avl-result-map-postcondition-p
       original datum tree-result)))))

(defun-sk
    ntp4vc-pearl-avl-tables-mapbase-insertqtvc-statement ()
  (forall (original datum)
    (implies
     (and
      (ntp4vc-avl-context-p)
      (ntp4vc-avl-t4-p original)
      (ntp4vc-avl-data-p datum))
     (let* ((original-tree
             (ntp4vc-avl-field original))
            (datum-key
             (ntp4vc-avl-key datum)))
       (and
        (ntp4vc-avl-selection-possible-p
         (ntp4vc-avl-model-seq original-tree))
        (ntp4vc-avl-tree-result-continuation-p
         original datum original-tree datum-key))))))

(value-triple :itpeval-statement-checked)
:q
