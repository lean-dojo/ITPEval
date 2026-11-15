;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/avl/priority_queue_PQueue_selected_partqtvc: the priority-queue
;; selected-part verification condition for choosing a pivot-relative split
;; from the aggregate minima of two sequences. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent one arbitrary inhabited source
;; item type, its arbitrary inhabited key type, the key map, and the source
;; total preorder.

(defstub spq-item-p (x) t)
(defstub spq-key-p (x) t)
(defstub spq-key (item) t)
(defstub spq-le-op (left right) t)
(defstub spq-balancing () t)

(defun spq-le-p (left right)
  (if (spq-le-op left right) t nil))

(defun spq-eq-p (left right)
  (and
   (spq-le-p left right)
   (spq-le-p right left)))

(defun spq-lt-p (left right)
  (and
   (spq-le-p left right)
   (not (spq-le-p right left))))

(defun spq-item-list-p (sequence)
  (if (endp sequence)
      (equal sequence nil)
    (and
     (spq-item-p (car sequence))
     (spq-item-list-p (cdr sequence)))))

;; Options are exact tagged values.

(defun spq-none ()
  (list :none))

(defun spq-some (value)
  (list :some value))

(defun spq-none-p (option)
  (equal option (spq-none)))

(defun spq-some-p (option)
  (and
   (true-listp option)
   (equal (len option) 2)
   (equal (car option) :some)))

(defun spq-option-value (option)
  (cadr option))

(defun spq-key-option-p (option)
  (or
   (spq-none-p option)
   (and
    (spq-some-p option)
    (spq-key-p
     (spq-option-value option)))))

(defun spq-item-option-p (option)
  (or
   (spq-none-p option)
   (and
    (spq-some-p option)
    (spq-item-p
     (spq-option-value option)))))

;; This is the source operation on optional keys, and its aggregate
;; specialized to measure_closure, which is definitionally Some composed
;; with the key map.

(defun spq-op (left right)
  (if (spq-none-p left)
      right
    (if (spq-none-p right)
        left
      (if (spq-lt-p
           (spq-option-value right)
           (spq-option-value left))
          right
        left))))

(defun spq-measure-closure (item)
  (spq-some (spq-key item)))

(defun spq-aggregate (sequence)
  (if (endp sequence)
      (spq-none)
    (spq-op
     (spq-measure-closure (car sequence))
     (spq-aggregate (cdr sequence)))))

;; Splits reproduce the SelectionTypes record exactly.

(defun spq-split (left middle right)
  (list :split left middle right))

(defun spq-split-p (split)
  (and
   (true-listp split)
   (equal (len split) 4)
   (equal (car split) :split)
   (spq-item-list-p (cadr split))
   (spq-item-option-p (caddr split))
   (spq-item-list-p (cadddr split))))

(defun spq-split-left (split)
  (cadr split))

(defun spq-split-middle (split)
  (caddr split))

(defun spq-split-right (split)
  (cadddr split))

(defun spq-option-to-sequence (option)
  (if (spq-none-p option)
      nil
    (list (spq-option-value option))))

(defun spq-rebuild (split)
  (append
   (append
    (spq-split-left split)
    (spq-option-to-sequence
     (spq-split-middle split)))
   (spq-split-right split)))

(defun spq-left-extend (left item split)
  (spq-split
   (append
    left
    (cons item
          (spq-split-left split)))
   (spq-split-middle split)
   (spq-split-right split)))

(defun spq-right-extend (split item right)
  (spq-split
   (spq-split-left split)
   (spq-split-middle split)
   (append
    (spq-split-right split)
    (cons item right))))

;; Recursive all-element predicates are equivalent to the source bounded
;; integer-index quantifiers on true lists.

(defun spq-lower-bound-p (key sequence)
  (if (endp sequence)
      t
    (and
     (spq-le-p key
               (spq-key (car sequence)))
     (spq-lower-bound-p
      key (cdr sequence)))))

(defun spq-lower-bound-strict-p (key sequence)
  (if (endp sequence)
      t
    (and
     (spq-lt-p key
               (spq-key (car sequence)))
     (spq-lower-bound-strict-p
      key (cdr sequence)))))

(defun spq-selected-p (split)
  (and
   (spq-some-p
    (spq-split-middle split))
   (let ((item
          (spq-option-value
           (spq-split-middle split))))
     (and
      (spq-lower-bound-p
       (spq-key item)
       (spq-split-right split))
      (spq-lower-bound-strict-p
       (spq-key item)
       (spq-split-left split))))))

(defun spq-selection-possible-p (sequence)
  (not (equal (len sequence) 0)))

;; part_base Unit has exactly these three inhabitants.

(defun spq-here ()
  (list :here))

(defun spq-left ()
  (list :left :unit))

(defun spq-right ()
  (list :right :unit))

(defun spq-part-result-p (result)
  (or
   (equal result (spq-here))
   (equal result (spq-left))
   (equal result (spq-right))))

;; A comparison integer has exactly the three source sign equivalences.

(defun spq-comparison-p (comparison left right)
  (and
   (integerp comparison)
   (iff (< 0 comparison)
        (spq-lt-p left right))
   (iff (< comparison 0)
        (spq-lt-p right left))
   (iff (equal comparison 0)
        (spq-eq-p right left))))

;; Each existential remains internal at the same branch where it occurs in
;; the source match.

(defun-sk spq-none-left-result-p (result left-key pivot-key)
  (exists (comparison)
    (and
     (spq-comparison-p
      comparison left-key pivot-key)
     (if (< comparison 0)
         (equal result (spq-here))
       (equal result (spq-left))))))

(defun-sk spq-right-none-result-p (result right-key pivot-key)
  (exists (comparison)
    (and
     (spq-comparison-p
      comparison right-key pivot-key)
     (if (<= comparison 0)
         (equal result (spq-here))
       (equal result (spq-right))))))

(defun-sk spq-both-left-inner-p (result pivot-key left-key)
  (exists (comparison)
    (and
     (spq-comparison-p
      comparison pivot-key left-key)
     (if (<= comparison 0)
         (equal result (spq-left))
       (equal result (spq-here))))))

(defun-sk spq-both-right-inner-p (result right-key left-key)
  (exists (comparison)
    (and
     (spq-comparison-p
      comparison right-key left-key)
     (if (<= comparison 0)
         (equal result (spq-left))
       (equal result (spq-right))))))

(defun-sk spq-both-result-p
    (result right-key left-key pivot-key)
  (exists (comparison)
    (and
     (spq-comparison-p
      comparison right-key pivot-key)
     (if (<= comparison 0)
         (spq-both-left-inner-p
          result pivot-key left-key)
       (spq-both-right-inner-p
        result right-key left-key)))))

(defun spq-operational-result-p
    (result item right-sequence left-sequence)
  (let ((right-aggregate
         (spq-aggregate right-sequence))
        (left-aggregate
         (spq-aggregate left-sequence))
        (pivot-key
         (spq-key item)))
    (if (spq-none-p right-aggregate)
        (if (spq-none-p left-aggregate)
            (equal result (spq-here))
          (spq-none-left-result-p
           result
           (spq-option-value left-aggregate)
           pivot-key))
      (if (spq-none-p left-aggregate)
          (spq-right-none-result-p
           result
           (spq-option-value right-aggregate)
           pivot-key)
        (spq-both-result-p
         result
         (spq-option-value right-aggregate)
         (spq-option-value left-aggregate)
         pivot-key)))))

;; The source's first match has True in every branch and is retained
;; structurally here.

(defun spq-initial-match-p (right-sequence left-sequence)
  (if (spq-none-p
       (spq-aggregate right-sequence))
      (if (spq-none-p
           (spq-aggregate left-sequence))
          t
        t)
    (if (spq-none-p
         (spq-aggregate left-sequence))
        t
      t)))

;; The continuation quantifiers range over every well-typed split, exactly as
;; in the Left and Right conclusions.

(defun-sk spq-all-left-continuations-p
    (item right-sequence left-sequence)
  (forall (split)
    (implies
     (spq-split-p split)
     (implies
      (and
       (spq-selected-p split)
       (equal
        (spq-rebuild split)
        left-sequence))
      (spq-selected-p
       (spq-right-extend
        split item right-sequence))))))

(defun-sk spq-all-right-continuations-p
    (item right-sequence left-sequence)
  (forall (split)
    (implies
     (spq-split-p split)
     (implies
      (and
       (spq-selected-p split)
       (equal
        (spq-rebuild split)
        right-sequence))
      (spq-selected-p
       (spq-left-extend
        left-sequence item split))))))

(defun spq-result-contract-p
    (result item right-sequence left-sequence)
  (if (equal result (spq-here))
      (spq-selected-p
       (spq-split
        left-sequence
        (spq-some item)
        right-sequence))
    (if (equal result (spq-left))
        (and
         (spq-selection-possible-p
          left-sequence)
         (spq-all-left-continuations-p
          item right-sequence left-sequence))
      (and
       (spq-selection-possible-p
        right-sequence)
       (spq-all-right-continuations-p
        item right-sequence left-sequence)))))

(defun-sk spq-all-results-p
    (item right-sequence left-sequence)
  (forall (result)
    (implies
     (spq-part-result-p result)
     (implies
      (spq-operational-result-p
       result item right-sequence left-sequence)
      (spq-result-contract-p
       result item right-sequence left-sequence)))))

;; The source type inhabitation, positive balancing constant, key closure,
;; total-preorder laws, and option-monoid laws are explicit assumptions.

(defun-sk spq-carriers-inhabited-p ()
  (exists (item key)
    (and
     (spq-item-p item)
     (spq-key-p key))))

(defun-sk spq-key-closure-p ()
  (forall (item)
    (implies
     (spq-item-p item)
     (spq-key-p
      (spq-key item)))))

(defun-sk spq-order-reflexive-p ()
  (forall (key)
    (implies
     (spq-key-p key)
     (spq-le-p key key))))

(defun-sk spq-order-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (spq-key-p x)
      (spq-key-p y)
      (spq-key-p z)
      (spq-le-p x y)
      (spq-le-p y z))
     (spq-le-p x z))))

(defun-sk spq-order-total-p ()
  (forall (x y)
    (implies
     (and
      (spq-key-p x)
      (spq-key-p y))
     (or
      (spq-le-p x y)
      (spq-le-p y x)))))

(defun-sk spq-op-associative-p ()
  (forall (a b c)
    (implies
     (and
      (spq-key-option-p a)
      (spq-key-option-p b)
      (spq-key-option-p c))
     (equal
      (spq-op a (spq-op b c))
      (spq-op (spq-op a b) c)))))

(defun-sk spq-op-neutral-p ()
  (forall (option)
    (implies
     (spq-key-option-p option)
     (and
      (equal
       (spq-op option (spq-none))
       option)
      (equal
       option
       (spq-op (spq-none) option))))))

(defun spq-background-p ()
  (and
   (natp (spq-balancing))
   (< 0 (spq-balancing))
   (spq-carriers-inhabited-p)
   (spq-key-closure-p)
   (spq-order-reflexive-p)
   (spq-order-transitive-p)
   (spq-order-total-p)
   (spq-op-associative-p)
   (spq-op-neutral-p)))

(defun-sk
  ntp4vc-pearl-avl-priority-queue-pqueue-selected-partqtvc-statement
  ()
  (forall (item right-sequence left-sequence)
    (implies
     (and
      (spq-background-p)
      (spq-item-p item)
      (spq-item-list-p right-sequence)
      (spq-item-list-p left-sequence))
     (and
      (spq-initial-match-p
       right-sequence left-sequence)
      (spq-all-results-p
       item right-sequence left-sequence)))))

(value-triple :itpeval-statement-checked)
:q
