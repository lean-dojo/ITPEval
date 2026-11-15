;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/linear_probing_LinearProbing_addqtvc: the verification condition for
;; adding a key to a linear-probing hash table while preserving its abstract
;; view and representation invariant. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The three predicates below give a standard relativized encoding of the
;; source's arbitrary key, key-model, and table-state types. They do not bound
;; or enumerate any carrier.

(defstub lp-add-key-p (x) t)
(defstub lp-add-keym-p (x) t)
(defstub lp-add-state-p (x) t)

(defstub lp-add-key-default () t)
(defstub lp-add-state-default () t)
(defstub lp-add-keym1 (key) t)
(defstub lp-add-hash (key) t)
(defstub lp-add-dummy () t)
(defstub lp-add-size (table) t)
(defstub lp-add-data (table) t)
(defstub lp-add-view (table modeled-key) t)
(defstub lp-add-loc (table modeled-key) t)

(defun lp-add-key-list-p (xs)
  (if (consp xs)
      (and (lp-add-key-p (car xs))
           (lp-add-key-list-p (cdr xs)))
    (equal xs nil)))

(defun lp-add-int-to-nat (z)
  (nfix z))

(defun lp-add-nth-default (n xs)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (if (consp xs)
          (car xs)
        (lp-add-key-default))
    (if (consp xs)
        (lp-add-nth-default (1- n) (cdr xs))
      (lp-add-key-default))))

;; This is Lean List.set: an out-of-range update leaves the list unchanged.

(defun lp-add-list-set (xs n value)
  (declare (xargs :measure (nfix n)))
  (if (consp xs)
      (if (zp n)
          (cons value (cdr xs))
        (cons (car xs)
              (lp-add-list-set (cdr xs) (1- n) value)))
    nil))

(defun lp-add-eq (x y)
  (equal (lp-add-keym1 x)
         (lp-add-keym1 y)))

(defun lp-add-neq (x y)
  (not (lp-add-eq x y)))

;; HASH is nonnegative and N is positive in the source context, so ACL2 MOD
;; is exactly the pinned Why3 ComputerDivision.mod remainder used by bucket.

(defun lp-add-bucket (key n)
  (if (and (integerp n)
           (< 0 n))
      (mod (lp-add-hash key) n)
    0))

(defun lp-add-between (left index right)
  (or (and (<= left index)
           (< index right))
      (and (< right left)
           (<= left index))
      (and (< index right)
           (< right left))))

(defun lp-add-fc (data index)
  (lp-add-eq
   (lp-add-nth-default
    (lp-add-int-to-nat index)
    data)
   (lp-add-dummy)))

;; NumOf.numof is uniquely characterized by its source recurrence. This
;; recursion counts exactly the same half-open integer interval [LOWER, UPPER).

(defun lp-add-numof-loop (data index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (if (lp-add-fc data index) 1 0)
       (lp-add-numof-loop
        data
        (+ 1 index)
        (1- remaining)))))

(defun lp-add-numof (data lower upper)
  (if (and (integerp lower)
           (integerp upper))
      (lp-add-numof-loop
       data
       lower
       (nfix (- upper lower)))
    0))

;; A descriptor consisting of a base table and at most one update represents
;; exactly the view and location functions occurring in the source statement.

(defun lp-add-view-value
    (base updated-p target value query)
  (if (and updated-p
           (equal query target))
      value
    (lp-add-view base query)))

(defun lp-add-loc-value
    (base updated-p target value query)
  (if (and updated-p
           (equal query target))
      value
    (lp-add-loc base query)))

(defun-sk lp-add-view-equal-p (left right)
  (forall (modeled-key)
    (implies
     (lp-add-keym-p modeled-key)
     (equal
      (lp-add-view left modeled-key)
      (lp-add-view right modeled-key)))))

(defun-sk lp-add-loc-equal-p (left right)
  (forall (modeled-key)
    (implies
     (lp-add-keym-p modeled-key)
     (equal
      (lp-add-loc left modeled-key)
      (lp-add-loc right modeled-key)))))

(defun-sk lp-add-view-update-equal-state-p
    (base target value table)
  (forall (modeled-key)
    (implies
     (lp-add-keym-p modeled-key)
     (equal
      (lp-add-view-value
       base t target value modeled-key)
      (lp-add-view table modeled-key)))))

(defun-sk lp-add-loc-update-equal-state-p
    (base target value table)
  (forall (modeled-key)
    (implies
     (lp-add-keym-p modeled-key)
     (equal
      (lp-add-loc-value
       base t target value modeled-key)
      (lp-add-loc table modeled-key)))))

(defun-sk lp-add-valid-data-indices-p
    (table-data
     view-base view-updated-p view-target view-value
     loc-base loc-updated-p loc-target loc-value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (len table-data)))
     (let ((key
            (lp-add-nth-default
             (lp-add-int-to-nat index)
             table-data)))
       (implies
        (lp-add-neq key (lp-add-dummy))
        (and
         (equal
          (lp-add-view-value
           view-base view-updated-p view-target view-value
           (lp-add-keym1 key))
          t)
         (equal
          (lp-add-loc-value
           loc-base loc-updated-p loc-target loc-value
           (lp-add-keym1 key))
          index)))))))

(defun-sk lp-add-valid-probe-path-p
    (table-data key location)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (len table-data))
      (lp-add-between
       (lp-add-bucket key (len table-data))
       index
       location))
     (and
      (lp-add-neq
       (lp-add-nth-default
        (lp-add-int-to-nat index)
        table-data)
       key)
      (lp-add-neq
       (lp-add-nth-default
        (lp-add-int-to-nat index)
        table-data)
       (lp-add-dummy))))))

(defun-sk lp-add-valid-view-keys-p
    (table-data
     view-base view-updated-p view-target view-value
     loc-base loc-updated-p loc-target loc-value)
  (forall (key)
    (implies
     (and
      (lp-add-key-p key)
      (equal
       (lp-add-view-value
        view-base view-updated-p view-target view-value
        (lp-add-keym1 key))
       t))
     (let ((location
            (lp-add-loc-value
             loc-base loc-updated-p loc-target loc-value
             (lp-add-keym1 key))))
       (and
        (integerp location)
        (<= 0 location)
        (< location (len table-data))
        (lp-add-eq
         (lp-add-nth-default
          (lp-add-int-to-nat location)
          table-data)
         key)
        (lp-add-valid-probe-path-p
         table-data key location))))))

(defun lp-add-valid-p
    (table-data
     view-base view-updated-p view-target view-value
     loc-base loc-updated-p loc-target loc-value)
  (and
   (not
    (equal
     (lp-add-view-value
      view-base view-updated-p view-target view-value
      (lp-add-keym1 (lp-add-dummy)))
     t))
   (lp-add-valid-data-indices-p
    table-data
    view-base view-updated-p view-target view-value
    loc-base loc-updated-p loc-target loc-value)
   (lp-add-valid-view-keys-p
    table-data
    view-base view-updated-p view-target view-value
    loc-base loc-updated-p loc-target loc-value)))

(defun lp-add-state-invariant-p (table)
  (and
   (<= 0 (lp-add-size table))
   (< (lp-add-size table)
      (len (lp-add-data table)))
   (equal
    (+ (lp-add-size table)
       (lp-add-numof
        (lp-add-data table)
        0
        (len (lp-add-data table))))
    (len (lp-add-data table)))
   (lp-add-valid-p
    (lp-add-data table)
    table nil nil nil
    table nil nil nil)))

(defun-sk lp-add-carrier-and-closure-laws-p ()
  (forall (key modeled-key table)
    (and
     (implies
      (lp-add-key-p key)
      (and
       (lp-add-keym-p (lp-add-keym1 key))
       (integerp (lp-add-hash key))))
     (implies
      (and
       (lp-add-state-p table)
       (lp-add-keym-p modeled-key))
      (and
       (booleanp (lp-add-view table modeled-key))
       (integerp (lp-add-loc table modeled-key))))
     (implies
      (lp-add-state-p table)
      (and
       (integerp (lp-add-size table))
       (lp-add-key-list-p (lp-add-data table)))))))

(defun-sk lp-add-hash-laws-p ()
  (forall (x y)
    (and
     (implies
      (lp-add-key-p x)
      (<= 0 (lp-add-hash x)))
     (implies
      (and
       (lp-add-key-p x)
       (lp-add-key-p y)
       (lp-add-eq x y))
      (equal
       (lp-add-hash x)
       (lp-add-hash y))))))

(defun-sk lp-add-all-state-invariants-p ()
  (forall (table)
    (implies
     (lp-add-state-p table)
     (lp-add-state-invariant-p table))))

(defun-sk lp-add-state-injectivity-p ()
  (forall (left right)
    (implies
     (and
      (lp-add-state-p left)
      (lp-add-state-p right)
      (equal
       (lp-add-size left)
       (lp-add-size right))
      (equal
       (lp-add-data left)
       (lp-add-data right))
      (lp-add-view-equal-p left right)
      (lp-add-loc-equal-p left right))
     (equal left right))))

(defun lp-add-source-context-p ()
  (and
   (lp-add-key-p (lp-add-key-default))
   (lp-add-key-p (lp-add-dummy))
   (lp-add-state-p (lp-add-state-default))
   (lp-add-carrier-and-closure-laws-p)
   (lp-add-hash-laws-p)
   (lp-add-all-state-invariants-p)
   (lp-add-state-injectivity-p)))

;; Extensional equality between the two integer-indexed functions in the
;; List.set branch of the source verification condition.

(defun-sk lp-add-nth-update-function-equal-p
    (table-data index value)
  (forall (argument)
    (implies
     (and
      (integerp argument)
      (<= 0 argument)
      (< argument (len table-data)))
     (equal
      (lp-add-nth-default
       (lp-add-int-to-nat argument)
       (lp-add-list-set
        table-data
        (lp-add-int-to-nat index)
        value))
      (if (equal argument index)
          value
        (lp-add-nth-default
         (lp-add-int-to-nat argument)
         table-data))))))

(defun-sk lp-add-resized-capacity-p (table)
  (forall (resized-state)
    (implies
     (lp-add-state-p resized-state)
     (implies
      (and
       (lp-add-view-equal-p table resized-state)
       (equal
        (lp-add-size table)
        (lp-add-size resized-state)))
      (implies
       (equal
        (len (lp-add-data resized-state))
        (* 2 (len (lp-add-data table))))
       (< (+ 1 (lp-add-size resized-state))
          (len (lp-add-data resized-state))))))))

(defun-sk lp-add-no-conflict-before-p
    (key table-data index)
  (forall (probe-index)
    (implies
     (and
      (integerp probe-index)
      (<= 0 probe-index)
      (< probe-index (len table-data))
      (lp-add-between
       (lp-add-bucket key (len table-data))
       probe-index
       index))
     (and
      (lp-add-neq
       (lp-add-nth-default
        (lp-add-int-to-nat probe-index)
        table-data)
       key)
      (lp-add-neq
       (lp-add-nth-default
        (lp-add-int-to-nat probe-index)
        table-data)
       (lp-add-dummy))))))

(defun-sk lp-add-new-key-h2-branch-p
    (key original-state table index)
  (forall (result-state)
    (implies
     (lp-add-state-p result-state)
     (let ((updated-data
            (lp-add-list-set
             (lp-add-data table)
             (lp-add-int-to-nat index)
             key))
           (modeled-key
            (lp-add-keym1 key)))
       (and
        (and
         (<= 0 (+ 1 (lp-add-size table)))
         (< (+ 1 (lp-add-size table))
            (len updated-data)))
        (equal
         (+ 1
            (lp-add-size table)
            (lp-add-numof
             updated-data
             0
             (len updated-data)))
         (len updated-data))
        (lp-add-valid-p
         updated-data
         table t modeled-key t
         table t modeled-key index)
        (implies
         (and
          (lp-add-loc-update-equal-state-p
           table modeled-key index result-state)
          (lp-add-view-update-equal-state-p
           table modeled-key t result-state)
          (equal
           updated-data
           (lp-add-data result-state))
          (equal
           (+ 1 (lp-add-size table))
           (lp-add-size result-state)))
         (lp-add-view-update-equal-state-p
          original-state modeled-key t result-state)))))))

(defun-sk lp-add-existing-key-h2-branch-p
    (key original-state table index)
  (forall (result-state)
    (implies
     (lp-add-state-p result-state)
     (let ((modeled-key
            (lp-add-keym1 key)))
       (and
        (and
         (<= 0 (lp-add-size table))
         (< (lp-add-size table)
            (len (lp-add-data table))))
        (equal
         (+ (lp-add-size table)
            (lp-add-numof
             (lp-add-data table)
             0
             (len (lp-add-data table))))
         (len (lp-add-data table)))
        (lp-add-valid-p
         (lp-add-data table)
         table t modeled-key t
         table t modeled-key index)
        (implies
         (and
          (lp-add-loc-update-equal-state-p
           table modeled-key index result-state)
          (lp-add-view-update-equal-state-p
           table modeled-key t result-state)
          (equal
           (lp-add-data table)
           (lp-add-data result-state))
          (equal
           (lp-add-size table)
           (lp-add-size result-state)))
         (lp-add-view-update-equal-state-p
          original-state modeled-key t result-state)))))))

(defun lp-add-probe-index-result-p
    (key original-state table index)
  (let* ((old-key
          (lp-add-nth-default
           (lp-add-int-to-nat index)
           (lp-add-data table)))
         (dummy
          (lp-add-dummy)))
    (and
     (<= 0 index)
     (< index (len (lp-add-data table)))
     (implies
      (equal
       (lp-add-eq old-key dummy)
       (equal
        (lp-add-keym1 old-key)
        (lp-add-keym1 dummy)))
      (if (lp-add-eq old-key dummy)
          (and
           (<= 0 index)
           (< index (len (lp-add-data table)))
           (implies
            (equal
             (len
              (lp-add-list-set
               (lp-add-data table)
               (lp-add-int-to-nat index)
               key))
             (len (lp-add-data table)))
            (implies
             (equal
              (len
               (lp-add-list-set
                (lp-add-data table)
                (lp-add-int-to-nat index)
                key))
              (len (lp-add-data table)))
             (implies
              (lp-add-nth-update-function-equal-p
               (lp-add-data table)
               index
               key)
              (lp-add-new-key-h2-branch-p
               key original-state table index)))))
        (lp-add-existing-key-h2-branch-p
         key original-state table index))))))

(defun-sk lp-add-all-probe-indices-p
    (key original-state table)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len (lp-add-data table)))
       (or
        (lp-add-eq
         (lp-add-nth-default
          (lp-add-int-to-nat index)
          (lp-add-data table))
         (lp-add-dummy))
        (lp-add-eq
         (lp-add-nth-default
          (lp-add-int-to-nat index)
          (lp-add-data table))
         key))
       (lp-add-no-conflict-before-p
        key
        (lp-add-data table)
        index))
      (lp-add-probe-index-result-p
       key original-state table index)))))

(defun lp-add-h1-body-p (key original-state table)
  (and
   (lp-add-neq key (lp-add-dummy))
   (< 0 (len (lp-add-data table)))
   (< 0
      (lp-add-numof
       (lp-add-data table)
       0
       (len (lp-add-data table))))
   (lp-add-all-probe-indices-p
    key original-state table)))

(defun-sk lp-add-all-h1-p (key original-state)
  (forall (table)
    (implies
     (lp-add-state-p table)
     (implies
      (and
       (lp-add-view-equal-p original-state table)
       (equal
        (lp-add-size original-state)
        (lp-add-size table)))
      (implies
       (< (+ 1 (lp-add-size table))
          (len (lp-add-data table)))
       (lp-add-h1-body-p
        key original-state table))))))

;; This predicate is the complete unproved add'vc proposition. The source
;; declarations are conservative interfaces whose laws occur explicitly in
;; the antecedent; the conclusion preserves both conjuncts and every nested
;; universal quantifier of the joint ground-truth statement.

(defun-sk ntp4vc-linear-probing-addqtvc-statement ()
  (forall (key table)
    (implies
     (and
      (lp-add-source-context-p)
      (lp-add-key-p key)
      (lp-add-state-p table)
      (lp-add-neq key (lp-add-dummy)))
     (and
      (if
       (<= (len (lp-add-data table))
           (* 2 (+ 1 (lp-add-size table))))
       (lp-add-resized-capacity-p table)
       (< (+ 1 (lp-add-size table))
          (len (lp-add-data table))))
      (lp-add-all-h1-p key table)))))

(value-triple :itpeval-statement-checked)
:q
