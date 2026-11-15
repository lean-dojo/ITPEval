;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/priority_queue_PQueue_minqtvc: the priority-queue minimum
;; verification condition relating a selected split to a present bag element
;; equal to the modeled minimum.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces retain the arbitrary item, key, and priority-queue
;; object carriers at a fixed arbitrary inhabited source type.

(defstub pxm-item-p (x) t)
(defstub pxm-key-p (x) t)
(defstub pxm-object-p (x) t)

(defstub pxm-key (item) t)
(defstub pxm-le-op (left right) t)
(defstub pxm-balancing () t)
(defstub pxm-repr (object) t)
(defstub pxm-m1 (object) t)
(defstub pxm-get-minimum-index (sequence) t)

(defun pxm-le-p (left right)
  (if (pxm-le-op left right) t nil))

(defun pxm-lt-p (left right)
  (and
   (pxm-le-p left right)
   (not (pxm-le-p right left))))

(defun pxm-item-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (pxm-item-p (car xs))
     (pxm-item-list-p (cdr xs)))))

;; Exact tagged options are shared by key options and item options, with their
;; carrier predicates imposed at each typed use.

(defun pxm-none ()
  (list :none))

(defun pxm-some (value)
  (list :some value))

(defun pxm-none-p (option)
  (equal option (pxm-none)))

(defun pxm-some-p (option)
  (and
   (true-listp option)
   (equal (len option) 2)
   (equal (car option) :some)))

(defun pxm-option-value (option)
  (cadr option))

(defun pxm-key-option-p (option)
  (or
   (pxm-none-p option)
   (and
    (pxm-some-p option)
    (pxm-key-p
     (pxm-option-value option)))))

(defun pxm-item-option-p (option)
  (or
   (pxm-none-p option)
   (and
    (pxm-some-p option)
    (pxm-item-p
     (pxm-option-value option)))))

;; The source option operation chooses the smaller present key.

(defun pxm-op (left right)
  (if (pxm-none-p left)
      right
    (if (pxm-none-p right)
        left
      (if (pxm-lt-p
           (pxm-option-value right)
           (pxm-option-value left))
          right
        left))))

(defun pxm-measure (item)
  (pxm-some (pxm-key item)))

(defun pxm-aggregate (sequence)
  (if (endp sequence)
      (pxm-none)
    (pxm-op
     (pxm-measure (car sequence))
     (pxm-aggregate (cdr sequence)))))

;; Empty trees are NIL. Nodes are exact records
;; (:TREE-NODE left item right natural-height key-option-summary).

(defun pxm-tree-empty-p (tree)
  (equal tree nil))

(defun pxm-tree-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 6)
   (equal (car tree) :tree-node)))

(defun pxm-tree-left (tree)
  (cadr tree))

(defun pxm-tree-item (tree)
  (caddr tree))

(defun pxm-tree-right (tree)
  (cadddr tree))

(defun pxm-tree-height (tree)
  (car (cddddr tree)))

(defun pxm-tree-summary (tree)
  (cadr (cddddr tree)))

(defun pxm-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (pxm-tree-empty-p tree)
      t
    (and
     (pxm-tree-node-shape-p tree)
     (pxm-tree-p (pxm-tree-left tree))
     (pxm-item-p (pxm-tree-item tree))
     (pxm-tree-p (pxm-tree-right tree))
     (natp (pxm-tree-height tree))
     (pxm-key-option-p
      (pxm-tree-summary tree)))))

;; The source model m is represented exactly as
;; (:M item-sequence integer-height).

(defun pxm-model-p (model)
  (and
   (true-listp model)
   (equal (len model) 3)
   (equal (car model) :m)
   (pxm-item-list-p (cadr model))
   (integerp (caddr model))))

(defun pxm-model-sequence (model)
  (cadr model))

(defun pxm-model-height (model)
  (caddr model))

(defun pxm-node-model (left item right)
  (append left (cons item right)))

(defun pxm-seq-model (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (pxm-tree-empty-p tree)
      nil
    (if (pxm-tree-node-shape-p tree)
        (pxm-node-model
         (pxm-seq-model (pxm-tree-left tree))
         (pxm-tree-item tree)
         (pxm-seq-model (pxm-tree-right tree)))
      nil)))

(defun pxm-real-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (pxm-tree-empty-p tree)
      0
    (if (pxm-tree-node-shape-p tree)
        (let ((left-height
               (pxm-real-height
                (pxm-tree-left tree)))
              (right-height
               (pxm-real-height
                (pxm-tree-right tree))))
          (+ 1
             (if (< left-height right-height)
                 right-height
               left-height)))
      0)))

(defun pxm-balanced-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (pxm-tree-empty-p tree)
      t
    (if (pxm-tree-node-shape-p tree)
        (let* ((left (pxm-tree-left tree))
               (right (pxm-tree-right tree))
               (difference
                (- (pxm-real-height right)
                   (pxm-real-height left))))
          (and
           (equal
            (pxm-tree-height tree)
            (pxm-real-height tree))
           (equal
            (pxm-tree-summary tree)
            (pxm-aggregate
             (pxm-seq-model tree)))
           (<= (- (pxm-balancing))
               difference)
           (<= difference
               (pxm-balancing))
           (pxm-balanced-p left)
           (pxm-balanced-p right)))
      nil)))

(defun pxm-sequence (object)
  (pxm-model-sequence
   (pxm-m1 object)))

(defun pxm-height (object)
  (pxm-model-height
   (pxm-m1 object)))

;; Splits preserve the source record exactly.

(defun pxm-split (left middle right)
  (list :split left middle right))

(defun pxm-split-p (split)
  (and
   (true-listp split)
   (equal (len split) 4)
   (equal (car split) :split)
   (pxm-item-list-p (cadr split))
   (pxm-item-option-p (caddr split))
   (pxm-item-list-p (cadddr split))))

(defun pxm-split-left (split)
  (cadr split))

(defun pxm-split-middle (split)
  (caddr split))

(defun pxm-split-right (split)
  (cadddr split))

(defun pxm-option-to-sequence (option)
  (if (pxm-none-p option)
      nil
    (list (pxm-option-value option))))

(defun pxm-rebuild (split)
  (append
   (append
    (pxm-split-left split)
    (pxm-option-to-sequence
     (pxm-split-middle split)))
   (pxm-split-right split)))

(defun pxm-lower-bound-p (key sequence)
  (if (endp sequence)
      t
    (and
     (pxm-le-p key
               (pxm-key (car sequence)))
     (pxm-lower-bound-p
      key (cdr sequence)))))

(defun pxm-lower-bound-strict-p (key sequence)
  (if (endp sequence)
      t
    (and
     (pxm-lt-p key
               (pxm-key (car sequence)))
     (pxm-lower-bound-strict-p
      key (cdr sequence)))))

(defun pxm-selected-p (split)
  (and
   (pxm-some-p
    (pxm-split-middle split))
   (let ((item
          (pxm-option-value
           (pxm-split-middle split))))
     (and
      (pxm-lower-bound-p
       (pxm-key item)
       (pxm-split-right split))
      (pxm-lower-bound-strict-p
       (pxm-key item)
       (pxm-split-left split))))))

(defun pxm-selection-possible-p (sequence)
  (not (equal (len sequence) 0)))

;; Int.toNat is NFIX on integer inputs. NTH is made total with the arbitrary
;; inhabited item witness required below, matching source list indexing.

(defstub pxm-default-item () t)

(defun pxm-nth-default (index sequence)
  (if (zp index)
      (if (endp sequence)
          (pxm-default-item)
        (car sequence))
    (if (endp sequence)
        (pxm-default-item)
      (pxm-nth-default
       (- index 1)
       (cdr sequence)))))

(defun pxm-take (count sequence)
  (if (or (zp count)
          (endp sequence))
      nil
    (cons
     (car sequence)
     (pxm-take
      (- count 1)
      (cdr sequence)))))

(defun pxm-drop (count sequence)
  (if (or (zp count)
          (endp sequence))
      sequence
    (pxm-drop
     (- count 1)
     (cdr sequence))))

(defun pxm-count (item sequence)
  (if (endp sequence)
      0
    (+ (if (equal item (car sequence))
           1
         0)
       (pxm-count item (cdr sequence)))))

;; These are the three projections of m3 after unfolding its source
;; constructor: occurrence bag, selected minimum, and sequence cardinality.

(defun pxm-m3-bag (object item)
  (pxm-count item
             (pxm-sequence object)))

(defun pxm-m3-minimum (object)
  (pxm-nth-default
   (nfix
    (pxm-get-minimum-index
     (pxm-sequence object)))
   (pxm-sequence object)))

(defun pxm-m3-card (object)
  (len (pxm-sequence object)))

;; The arbitrary source carriers, key function, total preorder, positive
;; balance bound, option monoid laws, representation invariant, injectivity,
;; and minimum-index specifications remain explicit statement assumptions.

(defun-sk pxm-carriers-inhabited-p ()
  (exists (item key object)
    (and
     (pxm-item-p item)
     (pxm-key-p key)
     (pxm-object-p object)
     (pxm-item-p (pxm-default-item)))))

(defun-sk pxm-function-closures-p ()
  (forall (item object)
    (and
     (implies
      (pxm-item-p item)
      (pxm-key-p
       (pxm-key item)))
     (implies
      (pxm-object-p object)
      (and
       (pxm-tree-p
        (pxm-repr object))
       (pxm-model-p
        (pxm-m1 object)))))))

(defun-sk pxm-order-reflexive-p ()
  (forall (key)
    (implies
     (pxm-key-p key)
     (pxm-le-p key key))))

(defun-sk pxm-order-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (pxm-key-p x)
      (pxm-key-p y)
      (pxm-key-p z)
      (pxm-le-p x y)
      (pxm-le-p y z))
     (pxm-le-p x z))))

(defun-sk pxm-order-total-p ()
  (forall (x y)
    (implies
     (and
      (pxm-key-p x)
      (pxm-key-p y))
     (or
      (pxm-le-p x y)
      (pxm-le-p y x)))))

(defun-sk pxm-op-closure-p ()
  (forall (left right)
    (implies
     (and
      (pxm-key-option-p left)
      (pxm-key-option-p right))
     (pxm-key-option-p
      (pxm-op left right)))))

(defun-sk pxm-op-associative-p ()
  (forall (a b c)
    (implies
     (and
      (pxm-key-option-p a)
      (pxm-key-option-p b)
      (pxm-key-option-p c))
     (equal
      (pxm-op a (pxm-op b c))
      (pxm-op (pxm-op a b) c)))))

(defun-sk pxm-op-neutral-p ()
  (forall (option)
    (implies
     (pxm-key-option-p option)
     (and
      (equal
       (pxm-op option (pxm-none))
       option)
      (equal
       option
       (pxm-op (pxm-none) option))))))

(defun-sk pxm-invariant-p ()
  (forall (object)
    (implies
     (pxm-object-p object)
     (let ((tree (pxm-repr object))
           (model (pxm-m1 object)))
       (and
        (pxm-balanced-p tree)
        (equal
         (pxm-model-sequence model)
         (pxm-seq-model tree))
        (equal
         (pxm-model-height model)
         (pxm-real-height tree)))))))

(defun-sk pxm-object-injective-p ()
  (forall (left right)
    (implies
     (and
      (pxm-object-p left)
      (pxm-object-p right)
      (equal
       (pxm-repr left)
       (pxm-repr right))
      (equal
       (pxm-m1 left)
       (pxm-m1 right)))
     (equal left right))))

(defun-sk pxm-minimum-index-laws-p ()
  (forall (sequence)
    (implies
     (pxm-item-list-p sequence)
     (implies
      (not (equal (len sequence) 0))
      (let* ((index
              (pxm-get-minimum-index sequence))
             (natural-index (nfix index))
             (item
              (pxm-nth-default
               natural-index sequence)))
        (and
         (integerp index)
         (<= 0 index)
         (< index (len sequence))
         (equal
          (pxm-aggregate sequence)
          (pxm-some
           (pxm-key item)))
         (pxm-lower-bound-strict-p
          (pxm-key item)
          (pxm-take
           natural-index sequence))
         (pxm-lower-bound-p
          (pxm-key item)
          (pxm-drop
           natural-index sequence))))))))

(defun pxm-background-p ()
  (and
   (natp (pxm-balancing))
   (< 0 (pxm-balancing))
   (pxm-carriers-inhabited-p)
   (pxm-function-closures-p)
   (pxm-order-reflexive-p)
   (pxm-order-transitive-p)
   (pxm-order-total-p)
   (pxm-op-closure-p)
   (pxm-op-associative-p)
   (pxm-op-neutral-p)
   (pxm-invariant-p)
   (pxm-object-injective-p)
   (pxm-minimum-index-laws-p)))

;; The source match on o2 is represented by exact item options.  Its None
;; branch equates the split middle with None; its Some branch equates the
;; middle with the same item.

(defun pxm-middle-matches-p (split item-option)
  (if (pxm-none-p item-option)
      (equal
       (pxm-split-middle split)
       (pxm-none))
    (equal
     (pxm-split-middle split)
     (pxm-some
      (pxm-option-value item-option)))))

;; This retains the source universal result quantifier.  For None its premise
;; is false; for Some d it applies exactly when result=d.

(defun-sk pxm-all-results-minimum-p (object item-option)
  (forall (result)
    (implies
     (pxm-item-p result)
     (implies
      (if (pxm-none-p item-option)
          nil
        (equal
         result
         (pxm-option-value item-option)))
      (and
       (< 0
          (pxm-m3-bag object result))
       (equal
        result
        (pxm-m3-minimum object)))))))

;; These are the source quantifiers over every split o1 and item option o2.

(defun-sk pxm-all-minimum-continuations-p (object)
  (forall (split item-option)
    (implies
     (and
      (pxm-split-p split)
      (pxm-item-option-p item-option))
     (implies
      (and
       (and
        (pxm-selected-p split)
        (equal
         (pxm-rebuild split)
         (pxm-sequence object)))
       (pxm-middle-matches-p
        split item-option))
      (and
       (pxm-some-p item-option)
       (pxm-all-results-minimum-p
        object item-option))))))

(defun-sk
  ntp4vc-pearl-avl-priority-queue-pqueue-minqtvc-statement ()
  (forall (object)
    (implies
     (and
      (pxm-background-p)
      (pxm-object-p object))
     (implies
      (< 0 (pxm-m3-card object))
      (and
       (pxm-selection-possible-p
        (pxm-sequence object))
       (pxm-all-minimum-continuations-p
        object))))))

(value-triple :itpeval-statement-checked)
:q
