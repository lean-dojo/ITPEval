;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/patience_PatienceAbstract_play_gameqtvc: the abstract patience
;; solitaire verification condition relating the final number of stacks to
;; the maximum length of a strictly increasing input subsequence.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Integer maps are concrete total functions represented by an integer
;; default followed by finitely many overrides.  The first matching override
;; wins, so PG-INT-MAP-UPDATE is a closed exact functional-update constructor.

(defun pg-int-update-p (entry)
  (and
   (true-listp entry)
   (equal (len entry) 2)
   (integerp (nth 0 entry))
   (integerp (nth 1 entry))))

(defun pg-int-updates-p (updates)
  (if (consp updates)
      (and
       (pg-int-update-p (car updates))
       (pg-int-updates-p (cdr updates)))
    (equal updates nil)))

(defun pg-make-int-map (default updates)
  (list :pg-int-map default updates))

(defun pg-int-map-p (map-object)
  (and
   (true-listp map-object)
   (equal (len map-object) 3)
   (equal (nth 0 map-object)
          :pg-int-map)
   (integerp (nth 1 map-object))
   (pg-int-updates-p
    (nth 2 map-object))))

(defun pg-int-updates-get
    (updates index default)
  (if (consp updates)
      (if (equal index
                 (nth 0 (car updates)))
          (nth 1 (car updates))
        (pg-int-updates-get
         (cdr updates) index default))
    default))

(defun pg-int-map-get (map-object index)
  (pg-int-updates-get
   (nth 2 map-object)
   index
   (nth 1 map-object)))

(defun pg-int-map-update
    (map-object index value)
  (pg-make-int-map
   (nth 1 map-object)
   (cons
    (list index value)
    (nth 2 map-object))))

;; A source map int -> map int int is equivalently a total function of two
;; integer arguments.  Its concrete code uses a default and finite overrides
;; keyed by (stack-index,height), with a closed exact update constructor.

(defun pg-stack-update-p (entry)
  (and
   (true-listp entry)
   (equal (len entry) 3)
   (integerp (nth 0 entry))
   (integerp (nth 1 entry))
   (integerp (nth 2 entry))))

(defun pg-stack-updates-p (updates)
  (if (consp updates)
      (and
       (pg-stack-update-p (car updates))
       (pg-stack-updates-p (cdr updates)))
    (equal updates nil)))

(defun pg-make-stack-map (default updates)
  (list :pg-stack-map default updates))

(defun pg-stack-map-p (map-object)
  (and
   (true-listp map-object)
   (equal (len map-object) 3)
   (equal (nth 0 map-object)
          :pg-stack-map)
   (integerp (nth 1 map-object))
   (pg-stack-updates-p
    (nth 2 map-object))))

(defun pg-stack-updates-get
    (updates stack-index height default)
  (if (consp updates)
      (if (and
           (equal stack-index
                  (nth 0 (car updates)))
           (equal height
                  (nth 1 (car updates))))
          (nth 2 (car updates))
        (pg-stack-updates-get
         (cdr updates)
         stack-index
         height
         default))
    default))

(defun pg-stack-map-get
    (map-object stack-index height)
  (pg-stack-updates-get
   (nth 2 map-object)
   stack-index
   height
   (nth 1 map-object)))

(defun pg-stack-map-update
    (map-object stack-index height value)
  (pg-make-stack-map
   (nth 1 map-object)
   (cons
    (list stack-index height value)
    (nth 2 map-object))))

;; Position maps use one shared override list for the pair result, preserving
;; the source function int -> (int,int).  Updates replace the complete pair.

(defun pg-position-update-p (entry)
  (and
   (true-listp entry)
   (equal (len entry) 3)
   (integerp (nth 0 entry))
   (integerp (nth 1 entry))
   (integerp (nth 2 entry))))

(defun pg-position-updates-p (updates)
  (if (consp updates)
      (and
       (pg-position-update-p (car updates))
       (pg-position-updates-p (cdr updates)))
    (equal updates nil)))

(defun pg-make-position-map
    (default-stack default-height updates)
  (list
   :pg-position-map
   default-stack
   default-height
   updates))

(defun pg-position-map-p (map-object)
  (and
   (true-listp map-object)
   (equal (len map-object) 4)
   (equal (nth 0 map-object)
          :pg-position-map)
   (integerp (nth 1 map-object))
   (integerp (nth 2 map-object))
   (pg-position-updates-p
    (nth 3 map-object))))

(defun pg-position-updates-stack
    (updates card-index default)
  (if (consp updates)
      (if (equal card-index
                 (nth 0 (car updates)))
          (nth 1 (car updates))
        (pg-position-updates-stack
         (cdr updates) card-index default))
    default))

(defun pg-position-updates-height
    (updates card-index default)
  (if (consp updates)
      (if (equal card-index
                 (nth 0 (car updates)))
          (nth 2 (car updates))
        (pg-position-updates-height
         (cdr updates) card-index default))
    default))

(defun pg-position-map-stack
    (map-object card-index)
  (pg-position-updates-stack
   (nth 3 map-object)
   card-index
   (nth 1 map-object)))

(defun pg-position-map-height
    (map-object card-index)
  (pg-position-updates-height
   (nth 3 map-object)
   card-index
   (nth 2 map-object)))

(defun pg-position-map-update
    (map-object card-index stack-index height)
  (pg-make-position-map
   (nth 1 map-object)
   (nth 2 map-object)
   (cons
    (list card-index stack-index height)
    (nth 3 map-object))))

;; Bidirectional finite-observation equivalence: decoding any valid concrete
;; map above yields a total source function, and each update constructor has
;; exactly the source point-update semantics.  Conversely, after fixing the
;; integer scalars and finite input list, every application that can affect
;; this VC lies in a finite bounded interval (card, stack, height, or sequence
;; indices).  Any source unary, stack, or position function can therefore be
;; encoded by choosing a default and overriding precisely those finitely many
;; observed arguments.  The source and concrete valuations then agree on all
;; formula-relevant applications.  Hence universal and existential function
;; quantifiers are preserved in both directions, not restricted to a finite
;; carrier or fixed table.

;; State and sequence records are concrete products.  Their source function
;; fields are rebuilt from the complete finite-pattern codes above.

(defun pg-make-state
    (num-stacks num-elts values-map stack-sizes-map
                stacks-map positions-map preds-map)
  (list
   num-stacks
   num-elts
   values-map
   stack-sizes-map
   stacks-map
   positions-map
   preds-map))

(defun pg-num-stacks (st)
  (nth 0 st))

(defun pg-num-elts (st)
  (nth 1 st))

(defun pg-values (st index)
  (pg-int-map-get
   (nth 2 st)
   index))

(defun pg-stack-sizes (st stack-index)
  (pg-int-map-get
   (nth 3 st)
   stack-index))

(defun pg-stacks (st stack-index height)
  (pg-stack-map-get
   (nth 4 st)
   stack-index
   height))

(defun pg-position-stack (st card-index)
  (pg-position-map-stack
   (nth 5 st)
   card-index))

(defun pg-position-height (st card-index)
  (pg-position-map-height
   (nth 5 st)
   card-index))

(defun pg-preds (st card-index)
  (pg-int-map-get
   (nth 6 st)
   card-index))

(defun pg-initial-state ()
  (pg-make-state
   0
   0
   (pg-make-int-map -1 nil)
   (pg-make-int-map 0 nil)
   (pg-make-stack-map -1 nil)
   (pg-make-position-map -1 -1 nil)
   (pg-make-int-map -1 nil)))

(defun pg-make-seq (seqlen seq-map)
  (list seqlen seq-map))

(defun pg-seqlen (sq)
  (nth 0 sq))

(defun pg-seqval (sq index)
  (pg-int-map-get
   (nth 1 sq)
   index))

(defun pg-integer-list-p (xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (pg-integer-list-p (cdr xs)))
    (equal xs nil)))

;; This is Why3's integer-to-natural conversion followed by total list
;; indexing with the source integer inhabitant as the out-of-range default.

(defun pg-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun pg-nth-int (index xs)
  (let ((natural-index
         (pg-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; Components of the abstract patience-state invariant.

(defun-sk pg-stack-contents-valid-p (st)
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
           (pg-num-stacks st)))
       (<= 1
           (pg-stack-sizes st stack-index)))
      (implies
       (and
        (<= 0 stack-index)
        (< stack-index
           (pg-num-stacks st))
        (<= 0 height)
        (< height
           (pg-stack-sizes st stack-index)))
       (and
        (<= 0
            (pg-stacks st stack-index height))
        (< (pg-stacks st stack-index height)
           (pg-num-elts st))))))))

(defun-sk pg-position-table-correct-p (st)
  (forall (card-index)
    (implies
     (integerp card-index)
     (implies
      (and
       (<= 0 card-index)
       (< card-index
          (pg-num-elts st)))
      (let ((stack-index
             (pg-position-stack st card-index))
            (height
             (pg-position-height st card-index)))
        (and
         (<= 0 stack-index)
         (< stack-index
            (pg-num-stacks st))
         (<= 0 height)
         (< height
            (pg-stack-sizes st stack-index))
         (equal
          (pg-stacks st stack-index height)
          card-index)))))))

(defun-sk pg-positions-inverse-p (st)
  (forall (stack-index height)
    (implies
     (and
      (integerp stack-index)
      (integerp height))
     (implies
      (and
       (<= 0 stack-index)
       (< stack-index
          (pg-num-stacks st))
       (<= 0 height)
       (< height
          (pg-stack-sizes st stack-index)))
      (let ((card-index
             (pg-stacks st stack-index height)))
        (and
         (equal
          (pg-position-stack st card-index)
          stack-index)
         (equal
          (pg-position-height st card-index)
          height)))))))

(defun-sk pg-stack-indices-increasing-p (st)
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
          (pg-num-stacks st))
       (<= 0 lower-height)
       (< lower-height upper-height)
       (< upper-height
          (pg-stack-sizes st stack-index)))
      (< (pg-stacks st stack-index lower-height)
         (pg-stacks st stack-index upper-height))))))

(defun-sk pg-stack-values-decreasing-p (st)
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
          (pg-num-stacks st))
       (<= 0 lower-height)
       (<= lower-height upper-height)
       (< upper-height
          (pg-stack-sizes st stack-index)))
      (<=
       (pg-values
        st
        (pg-stacks st stack-index upper-height))
       (pg-values
        st
        (pg-stacks st stack-index lower-height)))))))

(defun-sk pg-predecessors-valid-p (st)
  (forall (card-index)
    (implies
     (integerp card-index)
     (implies
      (and
       (<= 0 card-index)
       (< card-index
          (pg-num-elts st)))
      (let ((predecessor
             (pg-preds st card-index))
            (stack-index
             (pg-position-stack st card-index)))
        (and
         (<= -1 predecessor)
         (< predecessor
            (pg-num-elts st))
         (< predecessor card-index)
         (if (< predecessor 0)
             (equal stack-index 0)
           (and
            (< (pg-values st predecessor)
               (pg-values st card-index))
            (< 0 stack-index)
            (equal
             (pg-position-stack st predecessor)
             (- stack-index 1))))))))))

(defun pg-inv-p (st)
  (and
   (<= 0 (pg-num-stacks st))
   (<= (pg-num-stacks st)
       (pg-num-elts st))
   (implies
    (< 0 (pg-num-elts st))
    (< 0 (pg-num-stacks st)))
   (pg-stack-contents-valid-p st)
   (pg-position-table-correct-p st)
   (pg-positions-inverse-p st)
   (pg-stack-indices-increasing-p st)
   (pg-stack-values-decreasing-p st)
   (pg-predecessors-valid-p st)))

;; The source sequence record is a concrete pair consisting of an integer
;; length and a finite-pattern-complete integer-map code of input positions.

(defun-sk pg-sequence-indices-in-bounds-p (sq input)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i (pg-seqlen sq)))
      (and
       (<= 0 (pg-seqval sq i))
       (< (pg-seqval sq i)
          (len input)))))))

(defun-sk pg-sequence-indices-increasing-p (sq)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j))
     (implies
      (and
       (<= 0 i)
       (< i j)
       (< j (pg-seqlen sq)))
      (< (pg-seqval sq i)
         (pg-seqval sq j))))))

(defun-sk pg-sequence-values-increasing-p (sq input)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j))
     (implies
      (and
       (<= 0 i)
       (< i j)
       (< j (pg-seqlen sq)))
      (< (pg-nth-int
          (pg-seqval sq i)
          input)
         (pg-nth-int
          (pg-seqval sq j)
          input))))))

(defun pg-increasing-subsequence-p (sq input)
  (and
   (<= 0 (pg-seqlen sq))
   (<= (pg-seqlen sq)
       (len input))
   (pg-sequence-indices-in-bounds-p
    sq input)
   (pg-sequence-indices-increasing-p sq)
   (pg-sequence-values-increasing-p
    sq input)))

(defun-sk pg-maximal-sequence-exists-p (st input)
  (exists (seqlen seq-default seq-updates)
    (and
     (integerp seqlen)
     (integerp seq-default)
     (pg-int-updates-p seq-updates)
     (let ((sq
            (pg-make-seq
             seqlen
             (pg-make-int-map
              seq-default
              seq-updates))))
       (and
        (equal
         (pg-seqlen sq)
         (pg-num-stacks st))
        (pg-increasing-subsequence-p
         sq input))))))

(defun-sk pg-all-sequences-bounded-p (st input)
  (forall (seqlen seq-default seq-updates)
    (implies
     (and
      (integerp seqlen)
      (integerp seq-default)
      (pg-int-updates-p seq-updates))
     (let ((sq
            (pg-make-seq
             seqlen
             (pg-make-int-map
              seq-default
              seq-updates))))
       (implies
        (pg-increasing-subsequence-p
         sq input)
        (<= (pg-seqlen sq)
            (pg-num-stacks st)))))))

(defun pg-optimal-subsequence-result-p (st input)
  (and
   (pg-maximal-sequence-exists-p st input)
   (pg-all-sequences-bounded-p st input)))

;; Preconditions supplied by the completed call to play_cards.

(defun-sk pg-empty-prefix-values-p (st)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i 0))
      (equal
       (pg-values st i)
       -1)))))

(defun-sk pg-values-are-input-p (st input)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i (pg-num-elts st)))
      (equal
       (pg-values st i)
       (pg-nth-int i input))))))

;; Tail conditions for the descending loop's arbitrary sequence map.

(defun-sk pg-map-tail-bounds-p
    (st ns map-object lower)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (and
       (< lower j)
       (< j ns))
      (and
       (<= 0
           (pg-int-map-get map-object j))
       (< (pg-int-map-get map-object j)
          (pg-num-elts st)))))))

(defun-sk pg-map-tail-indices-increasing-p
    (ns map-object lower)
  (forall (j k)
    (implies
     (and
      (integerp j)
      (integerp k))
     (implies
      (and
       (< lower j)
       (< j k)
       (< k ns))
      (< (pg-int-map-get map-object j)
         (pg-int-map-get map-object k))))))

(defun-sk pg-map-tail-values-increasing-p
    (st ns map-object lower)
  (forall (j k)
    (implies
     (and
      (integerp j)
      (integerp k))
     (implies
      (and
       (< lower j)
       (< j k)
       (< k ns))
      (< (pg-values
          st
          (pg-int-map-get map-object j))
         (pg-values
          st
          (pg-int-map-get map-object k)))))))

;; The first loop invariant uses Const.const(-1), represented directly.

(defun-sk pg-constant-tail-bounds-p (st ns lower)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (and
       (< lower j)
       (< j ns))
      (and
       (<= 0 -1)
       (< -1 (pg-num-elts st)))))))

(defun-sk pg-constant-tail-indices-increasing-p
    (ns lower)
  (forall (j k)
    (implies
     (and
      (integerp j)
      (integerp k))
     (implies
      (and
       (< lower j)
       (< j k)
       (< k ns))
      (< -1 -1)))))

(defun-sk pg-constant-tail-values-increasing-p
    (st ns lower)
  (forall (j k)
    (implies
     (and
      (integerp j)
      (integerp k))
     (implies
      (and
       (< lower j)
       (< j k)
       (< k ns))
      (< (pg-values st -1)
         (pg-values st -1))))))

(defun pg-initial-loop-state-p
    (st ns o2 o4)
  (and
   (<= -1 o2)
   (< o2 (pg-num-elts st))
   (implies
    (<= 0 o4)
    (and
     (<= 0 o2)
     (equal
      (pg-position-stack st o2)
      o4)))
   (implies
    (< (+ o4 1) ns)
    (< o2 -1))
   (implies
    (and
     (<= 0 o4)
     (< o4 (- ns 1)))
    (< (pg-values st o2)
       (pg-values st -1)))
   (pg-constant-tail-bounds-p
    st ns o4)
   (pg-constant-tail-indices-increasing-p
    ns o4)
   (pg-constant-tail-values-increasing-p
    st ns o4)))

(defun pg-loop-state-p
    (st ns o4 map-object idx i)
  (and
   (<= i o4)
   (<= 0 i)
   (<= -1 idx)
   (< idx (pg-num-elts st))
   (implies
    (<= 0 i)
    (and
     (<= 0 idx)
     (equal
      (pg-position-stack st idx)
      i)))
   (implies
    (< (+ i 1) ns)
    (< idx
       (pg-int-map-get
        map-object
        (+ i 1))))
   (implies
    (and
     (<= 0 i)
     (< i (- ns 1)))
    (< (pg-values st idx)
       (pg-values
        st
        (pg-int-map-get
         map-object
         (+ i 1)))))
   (pg-map-tail-bounds-p
    st ns map-object i)
   (pg-map-tail-indices-increasing-p
    ns map-object i)
   (pg-map-tail-values-increasing-p
    st ns map-object i)))

(defun pg-map-update-value
    (map-object update-index update-value query-index)
  (pg-int-map-get
   (pg-int-map-update
    map-object update-index update-value)
   query-index))

(defun-sk pg-updated-tail-bounds-p
    (st ns map-object update-index update-value lower)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (and
       (< lower j)
       (< j ns))
      (and
       (<= 0
           (pg-map-update-value
            map-object update-index update-value j))
       (< (pg-map-update-value
           map-object update-index update-value j)
          (pg-num-elts st)))))))

(defun-sk pg-updated-tail-indices-increasing-p
    (ns map-object update-index update-value lower)
  (forall (j k)
    (implies
     (and
      (integerp j)
      (integerp k))
     (implies
      (and
       (< lower j)
       (< j k)
       (< k ns))
      (< (pg-map-update-value
          map-object update-index update-value j)
         (pg-map-update-value
          map-object update-index update-value k))))))

(defun-sk pg-updated-tail-values-increasing-p
    (st ns map-object update-index update-value lower)
  (forall (j k)
    (implies
     (and
      (integerp j)
      (integerp k))
     (implies
      (and
       (< lower j)
       (< j k)
       (< k ns))
      (< (pg-values
          st
          (pg-map-update-value
           map-object update-index update-value j))
         (pg-values
          st
          (pg-map-update-value
           map-object update-index update-value k)))))))

(defun pg-loop-step-result-p
    (st ns map-object idx i)
  (let* ((predecessor
          (pg-preds st idx))
         (next-i
          (- i 1)))
    (and
     (<= -1 predecessor)
     (< predecessor
        (pg-num-elts st))
     (implies
      (<= 0 next-i)
      (and
       (<= 0 predecessor)
       (equal
        (pg-position-stack st predecessor)
        next-i)))
     (implies
      (< (+ next-i 1) ns)
      (< predecessor
         (pg-map-update-value
          map-object i idx (+ next-i 1))))
     (implies
      (and
       (<= 0 next-i)
       (< next-i (- ns 1)))
      (< (pg-values st predecessor)
         (pg-values
          st
          (pg-map-update-value
           map-object i idx (+ next-i 1)))))
     (pg-updated-tail-bounds-p
      st ns map-object i idx next-i)
     (pg-updated-tail-indices-increasing-p
      ns map-object i idx next-i)
     (pg-updated-tail-values-increasing-p
      st ns map-object i idx next-i))))

(defun-sk pg-all-loop-steps-p
    (st ns o4 map-object idx)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (pg-loop-state-p
       st ns o4 map-object idx i)
      (pg-loop-step-result-p
       st ns map-object idx i)))))

;; This is the final invariant at loop index -1.  The source VC omits the
;; nonnegative-index conjunct here, so it remains a separate predicate.

(defun pg-final-loop-state-p
    (st ns map-object idx)
  (and
   (<= -1 idx)
   (< idx (pg-num-elts st))
   (implies
    (<= 0 -1)
    (and
     (<= 0 idx)
     (equal
      (pg-position-stack st idx)
      -1)))
   (implies
    (< (+ -1 1) ns)
    (< idx
       (pg-int-map-get
        map-object
        (+ -1 1))))
   (implies
    (and
     (<= 0 -1)
     (< -1 (- ns 1)))
    (< (pg-values st idx)
       (pg-values
        st
        (pg-int-map-get
         map-object
         (+ -1 1)))))
   (pg-map-tail-bounds-p
    st ns map-object -1)
   (pg-map-tail-indices-increasing-p
    ns map-object -1)
   (pg-map-tail-values-increasing-p
    st ns map-object -1)))

(defun-sk pg-all-loop-configurations-p
    (st input ns o4)
  (forall (seq-default seq-updates idx)
    (implies
     (and
      (integerp seq-default)
      (pg-int-updates-p seq-updates)
      (integerp idx))
     (let ((map-object
            (pg-make-int-map
             seq-default seq-updates)))
       (and
        (pg-all-loop-steps-p
         st ns o4 map-object idx)
        (implies
         (pg-final-loop-state-p
          st ns map-object idx)
         (pg-optimal-subsequence-result-p
          st input)))))))

(defun pg-game-branch-p (st input)
  (let ((ns (pg-num-stacks st)))
    (if (equal ns 0)
        (pg-optimal-subsequence-result-p
         st input)
      (let* ((o2
              (pg-stacks
               st
               (- ns 1)
               (- (pg-stack-sizes st (- ns 1))
                  1)))
             (o4 (- ns 1)))
        (and
         (implies
          (<= -1 o4)
          (and
           (pg-initial-loop-state-p
            st ns o2 o4)
           (pg-all-loop-configurations-p
            st input ns o4)))
         (implies
          (< o4 -1)
          (pg-optimal-subsequence-result-p
           st input)))))))

(defun-sk pg-all-completed-games-p (input)
  (forall (num-stacks num-elts
                      values-default values-updates
                      stack-sizes-default stack-sizes-updates
                      stacks-default stacks-updates
                      positions-default-stack positions-default-height
                      positions-updates
                      preds-default preds-updates)
    (implies
     (and
      (integerp num-stacks)
      (integerp num-elts)
      (integerp values-default)
      (pg-int-updates-p values-updates)
      (integerp stack-sizes-default)
      (pg-int-updates-p stack-sizes-updates)
      (integerp stacks-default)
      (pg-stack-updates-p stacks-updates)
      (integerp positions-default-stack)
      (integerp positions-default-height)
      (pg-position-updates-p positions-updates)
      (integerp preds-default)
      (pg-int-updates-p preds-updates))
     (let ((st
            (pg-make-state
             num-stacks
             num-elts
             (pg-make-int-map
              values-default values-updates)
             (pg-make-int-map
              stack-sizes-default
              stack-sizes-updates)
             (pg-make-stack-map
              stacks-default stacks-updates)
             (pg-make-position-map
              positions-default-stack
              positions-default-height
              positions-updates)
             (pg-make-int-map
              preds-default preds-updates))))
       (implies
        (and
         (pg-inv-p st)
         (equal
          (pg-num-elts st)
          (+ 0 (len input)))
         (pg-empty-prefix-values-p st)
         (pg-values-are-input-p st input))
        (pg-game-branch-p st input))))))

(defun
  ntp4vc-pearl-patience-patienceabstract-play-gameqtvc-statement
  (input)
  (implies
   (pg-integer-list-p input)
   (and
    (pg-inv-p (pg-initial-state))
    (pg-all-completed-games-p input))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
