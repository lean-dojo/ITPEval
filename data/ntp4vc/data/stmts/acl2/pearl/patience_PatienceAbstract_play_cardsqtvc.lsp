;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/patience_PatienceAbstract_play_cardsqtvc: the recursive patience-card
;; verification condition preserving the abstract state invariant, card count,
;; prior values, and the values appended from the input list.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source state is observed only through its record fields.  These
;; conservative interfaces retain the arbitrary state carrier and its total
;; integer-indexed maps; all source typing laws are explicit below.

(defstub pc-state-p (st) t)
(defstub pc-num-stacks (st) t)
(defstub pc-num-elts (st) t)
(defstub pc-values (st index) t)
(defstub pc-stack-sizes (st stack-index) t)
(defstub pc-stacks (st stack-index height) t)
(defstub pc-position-stack (st card-index) t)
(defstub pc-position-height (st card-index) t)
(defstub pc-preds (st card-index) t)

(defun-sk pc-state-domain-nonempty-p ()
  (exists (st)
    (pc-state-p st)))

(defun-sk pc-state-field-types-p ()
  (forall (st i j)
    (and
     (implies
      (pc-state-p st)
      (and
       (integerp (pc-num-stacks st))
       (integerp (pc-num-elts st))))
     (implies
      (and
       (pc-state-p st)
       (integerp i))
      (and
       (integerp (pc-values st i))
       (integerp (pc-stack-sizes st i))
       (integerp (pc-position-stack st i))
       (integerp (pc-position-height st i))
       (integerp (pc-preds st i))))
     (implies
      (and
       (pc-state-p st)
       (integerp i)
       (integerp j))
      (integerp (pc-stacks st i j))))))

(defun pc-source-context-p ()
  (and
   (pc-state-domain-nonempty-p)
   (pc-state-field-types-p)))

(defun pc-integer-list-p (xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (pc-integer-list-p (cdr xs)))
    (equal xs nil)))

;; This is Int.toNat followed by total list indexing with the source integer
;; inhabitant as the out-of-range default.

(defun pc-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun pc-nth-int (index xs)
  (let ((natural-index
         (pc-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; Components of the source abstract-state invariant.

(defun-sk pc-stack-contents-valid-p (st)
  (forall (stack-index height)
    (implies
     (and
      (integerp stack-index)
      (integerp height))
     (and
      (implies
       (and
        (<= 0 stack-index)
        (< stack-index
           (pc-num-stacks st)))
       (<= 1
           (pc-stack-sizes st stack-index)))
      (implies
       (and
        (<= 0 stack-index)
        (< stack-index
           (pc-num-stacks st))
        (<= 0 height)
        (< height
           (pc-stack-sizes st stack-index)))
       (and
        (<= 0
            (pc-stacks st stack-index height))
        (< (pc-stacks st stack-index height)
           (pc-num-elts st))))))))

(defun-sk pc-position-table-correct-p (st)
  (forall (card-index)
    (implies
     (integerp card-index)
     (implies
      (and
       (<= 0 card-index)
       (< card-index
          (pc-num-elts st)))
      (let ((stack-index
             (pc-position-stack st card-index))
            (height
             (pc-position-height st card-index)))
        (and
         (<= 0 stack-index)
         (< stack-index
            (pc-num-stacks st))
         (<= 0 height)
         (< height
            (pc-stack-sizes st stack-index))
         (equal
          (pc-stacks st stack-index height)
          card-index)))))))

(defun-sk pc-positions-inverse-p (st)
  (forall (stack-index height)
    (implies
     (and
      (integerp stack-index)
      (integerp height))
     (implies
      (and
       (<= 0 stack-index)
       (< stack-index
          (pc-num-stacks st))
       (<= 0 height)
       (< height
          (pc-stack-sizes st stack-index)))
      (let ((card-index
             (pc-stacks st stack-index height)))
        (and
         (equal
          (pc-position-stack st card-index)
          stack-index)
         (equal
          (pc-position-height st card-index)
          height)))))))

(defun-sk pc-stack-indices-increasing-p (st)
  (forall (stack-index lower-height upper-height)
    (implies
     (and
      (integerp stack-index)
      (integerp lower-height)
      (integerp upper-height))
     (implies
      (and
       (<= 0 stack-index)
       (< stack-index
          (pc-num-stacks st))
       (<= 0 lower-height)
       (< lower-height upper-height)
       (< upper-height
          (pc-stack-sizes st stack-index)))
      (< (pc-stacks st stack-index lower-height)
         (pc-stacks st stack-index upper-height))))))

(defun-sk pc-stack-values-decreasing-p (st)
  (forall (stack-index lower-height upper-height)
    (implies
     (and
      (integerp stack-index)
      (integerp lower-height)
      (integerp upper-height))
     (implies
      (and
       (<= 0 stack-index)
       (< stack-index
          (pc-num-stacks st))
       (<= 0 lower-height)
       (<= lower-height upper-height)
       (< upper-height
          (pc-stack-sizes st stack-index)))
      (<=
       (pc-values
        st
        (pc-stacks st stack-index upper-height))
       (pc-values
        st
        (pc-stacks st stack-index lower-height)))))))

(defun-sk pc-predecessors-valid-p (st)
  (forall (card-index)
    (implies
     (integerp card-index)
     (implies
      (and
       (<= 0 card-index)
       (< card-index
          (pc-num-elts st)))
      (let ((predecessor
             (pc-preds st card-index))
            (stack-index
             (pc-position-stack st card-index)))
        (and
         (<= -1 predecessor)
         (< predecessor
            (pc-num-elts st))
         (< predecessor card-index)
         (if (< predecessor 0)
             (equal stack-index 0)
           (and
            (< (pc-values st predecessor)
               (pc-values st card-index))
            (< 0 stack-index)
            (equal
             (pc-position-stack st predecessor)
             (- stack-index 1))))))))))

(defun pc-inv-p (st)
  (and
   (pc-state-p st)
   (<= 0 (pc-num-stacks st))
   (<= (pc-num-stacks st)
       (pc-num-elts st))
   (implies
    (< 0 (pc-num-elts st))
    (< 0 (pc-num-stacks st)))
   (pc-stack-contents-valid-p st)
   (pc-position-table-correct-p st)
   (pc-positions-inverse-p st)
   (pc-stack-indices-increasing-p st)
   (pc-stack-values-decreasing-p st)
   (pc-predecessors-valid-p st)))

;; Equality with the functional update values(num_elts := card) is pointwise
;; equality over the complete integer domain.

(defun-sk pc-values-single-update-p
    (new-state old-state card)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (pc-values new-state index)
      (if (equal index
                 (pc-num-elts old-state))
          card
        (pc-values old-state index))))))

(defun-sk pc-values-agree-range-p
    (new-state old-state lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (pc-values new-state index)
       (pc-values old-state index))))))

(defun-sk pc-values-from-list-p
    (st base lower upper xs)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (pc-values st index)
       (pc-nth-int (- index base) xs))))))

(defun pc-s2-conclusion-p
    (initial-state input final-state)
  (and
   (pc-inv-p final-state)
   (equal
    (pc-num-elts final-state)
    (+ (pc-num-elts initial-state)
       (len input)))
   (pc-values-agree-range-p
    final-state
    initial-state
    0
    (pc-num-elts initial-state))
   (pc-values-from-list-p
    final-state
    (pc-num-elts initial-state)
    (pc-num-elts initial-state)
    (pc-num-elts final-state)
    input)))

(defun-sk pc-all-s2-p
    (initial-state input intermediate-state remainder)
  (forall (final-state)
    (implies
     (pc-state-p final-state)
     (implies
      (and
       (pc-inv-p final-state)
       (equal
        (pc-num-elts final-state)
        (+ (pc-num-elts intermediate-state)
           (len remainder)))
       (pc-values-agree-range-p
        final-state
        intermediate-state
        0
        (pc-num-elts intermediate-state))
       (pc-values-from-list-p
        final-state
        (pc-num-elts intermediate-state)
        (pc-num-elts intermediate-state)
        (pc-num-elts final-state)
        remainder))
      (pc-s2-conclusion-p
       initial-state input final-state)))))

(defun-sk pc-all-s1-p (initial-state input)
  (forall (intermediate-state)
    (implies
     (pc-state-p intermediate-state)
     (implies
      (and
       (pc-inv-p intermediate-state)
       (equal
        (pc-num-elts intermediate-state)
        (+ (pc-num-elts initial-state) 1))
       (pc-values-single-update-p
        intermediate-state
        initial-state
        (car input)))
      (and
       ;; In the Cons branch, the source match reduces definitionally to
       ;; equality of the bound remainder with the input tail.
       (equal (cdr input) (cdr input))
       (pc-inv-p intermediate-state)
       (pc-all-s2-p
        initial-state
        input
        intermediate-state
        (cdr input)))))))

(defun pc-play-cards-vc-p (st input)
  (if (endp input)
      (and
       (pc-inv-p st)
       (equal
        (pc-num-elts st)
        (+ (pc-num-elts st)
           (len input)))
       (pc-values-from-list-p
        st
        (pc-num-elts st)
        (pc-num-elts st)
        (pc-num-elts st)
        input))
    (and
     (pc-inv-p st)
     (pc-all-s1-p st input))))

(defun-sk
  ntp4vc-pearl-patience-patienceabstract-play-cardsqtvc-statement
  ()
  (forall (st input)
    (implies
     (and
      (pc-source-context-p)
      (pc-state-p st)
      (pc-integer-list-p input)
      (pc-inv-p st))
     (pc-play-cards-vc-p st input))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
