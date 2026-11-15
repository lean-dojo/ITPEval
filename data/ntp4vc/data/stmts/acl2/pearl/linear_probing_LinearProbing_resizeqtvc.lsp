;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/linear_probing_LinearProbing_resizeqtvc: the pinned Why3 resize
;; verification condition for a linear-probing hash table, preserving its
;; representation invariants while reinserting entries into a table of
;; doubled length. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These recognizers relativize ACL2's universe to the source's arbitrary key,
;; modeled-key, and table-state types. They do not bound or enumerate a
;; carrier. Location maps inhabit a nonempty extensional function carrier
;; containing the zero map and closed under integer-valued point updates.

(defstub lp-resize-key-p (x) t)
(defstub lp-resize-keym-p (x) t)
(defstub lp-resize-state-p (x) t)

(defstub lp-resize-key-default () t)
(defstub lp-resize-keym-default () t)
(defstub lp-resize-state-default () t)
(defstub lp-resize-keym1 (key) t)
(defstub lp-resize-hash (key) t)
(defstub lp-resize-dummy () t)
(defstub lp-resize-size (table) t)
(defstub lp-resize-data (table) t)
(defstub lp-resize-view (table modeled-key) t)
(defstub lp-resize-loc-fn-p (function) t)
(defstub lp-resize-loc-fn-zero () t)
(defstub lp-resize-loc-fn-update (function modeled-key value) t)
(defstub lp-resize-loc-fn-apply (function modeled-key) t)
(defstub lp-resize-loc-map (table) t)

(defun lp-resize-loc (table modeled-key)
  (lp-resize-loc-fn-apply
   (lp-resize-loc-map table)
   modeled-key))

(defun lp-resize-key-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (lp-resize-key-p (car xs))
       (lp-resize-key-list-p (cdr xs)))
    (equal xs nil)))

;; INT.TONAT maps negative integers to zero. Source list lookup returns the
;; inhabited key default when that natural index lies outside the list.

(defun lp-resize-nth (index xs)
  (if (< (nfix index) (len xs))
      (nth (nfix index) xs)
    (lp-resize-key-default)))

;; This is source List.set: an out-of-range update leaves the list unchanged.

(defun lp-resize-set-nat (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (lp-resize-set-nat
        (cdr xs)
        (- index 1)
        value)))))

(defun lp-resize-set (xs index value)
  (lp-resize-set-nat xs (nfix index) value))

;; Equality and disequality are definitionally equality and disequality of the
;; modeled keys, as required by eq'spec and neq'spec.

(defun lp-resize-eq-p (x y)
  (equal
   (lp-resize-keym1 x)
   (lp-resize-keym1 y)))

(defun lp-resize-neq-p (x y)
  (not (lp-resize-eq-p x y)))

(defun lp-resize-between-p (left point right)
  (or
   (and
    (<= left point)
    (< point right))
   (and
    (< right left)
    (<= left point))
   (and
    (< point right)
    (< right left))))

;; HASH is nonnegative in the source context. For positive N, ACL2 MOD is the
;; Euclidean remainder specified by Why3 int.ComputerDivision.mod.

(defun lp-resize-bucket (key n)
  (if (and
       (integerp n)
       (< 0 n))
      (mod (lp-resize-hash key) n)
    0))

;; This recursion is NumOf.numof's source recurrence on [LOWER, UPPER).

(defun lp-resize-numof-loop (xs index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
      (lp-resize-eq-p
       (lp-resize-nth index xs)
       (lp-resize-dummy))
      1
      0)
     (lp-resize-numof-loop
      xs
      (+ index 1)
      (- remaining 1)))))

(defun lp-resize-numof (xs lower upper)
  (if (and
       (integerp lower)
       (integerp upper))
      (lp-resize-numof-loop
       xs
       lower
       (nfix (- upper lower)))
    0))

;; Function objects are extensional on the arbitrary modeled-key carrier.

(defun-sk lp-resize-loc-functions-pointwise-equal-p (left right)
  (forall (modeled-key)
    (implies
     (lp-resize-keym-p modeled-key)
     (equal
      (lp-resize-loc-fn-apply left modeled-key)
      (lp-resize-loc-fn-apply right modeled-key)))))

(defun-sk lp-resize-loc-function-laws-p ()
  (forall (function target value query left right)
    (and
     (implies
      (and
       (lp-resize-loc-fn-p function)
       (lp-resize-keym-p query))
      (integerp
       (lp-resize-loc-fn-apply function query)))
     (implies
      (lp-resize-keym-p query)
      (equal
       (lp-resize-loc-fn-apply
        (lp-resize-loc-fn-zero)
        query)
       0))
     (implies
      (and
       (lp-resize-loc-fn-p function)
       (lp-resize-keym-p target)
       (integerp value))
      (and
       (lp-resize-loc-fn-p
        (lp-resize-loc-fn-update
         function target value))
       (implies
        (lp-resize-keym-p query)
        (equal
         (lp-resize-loc-fn-apply
          (lp-resize-loc-fn-update
           function target value)
          query)
         (if (equal query target)
             value
           (lp-resize-loc-fn-apply
            function query))))))
     (implies
      (and
       (lp-resize-loc-fn-p left)
       (lp-resize-loc-fn-p right)
       (lp-resize-loc-functions-pointwise-equal-p
        left right))
      (equal left right)))))

(defun-sk lp-resize-view-equal-p (left right)
  (forall (modeled-key)
    (implies
     (lp-resize-keym-p modeled-key)
     (equal
      (lp-resize-view left modeled-key)
      (lp-resize-view right modeled-key)))))

(defun lp-resize-loc-equal-p (left right)
  (equal
   (lp-resize-loc-map left)
   (lp-resize-loc-map right)))

(defun-sk lp-resize-valid-data-indices-p
    (xs view-table loc-function)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (len xs)))
     (let ((key (lp-resize-nth index xs)))
       (implies
        (lp-resize-neq-p key (lp-resize-dummy))
        (and
         (equal
         (lp-resize-view
           view-table (lp-resize-keym1 key))
          t)
         (equal
          (lp-resize-loc-fn-apply
           loc-function
           (lp-resize-keym1 key))
          index)))))))

(defun-sk lp-resize-valid-probe-path-p
    (xs key location)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (len xs))
      (lp-resize-between-p
       (lp-resize-bucket key (len xs))
       index
       location))
     (and
      (lp-resize-neq-p
       (lp-resize-nth index xs)
       key)
      (lp-resize-neq-p
       (lp-resize-nth index xs)
       (lp-resize-dummy))))))

(defun-sk lp-resize-valid-view-keys-p
    (xs view-table loc-function)
  (forall (key)
    (implies
     (and
      (lp-resize-key-p key)
      (equal
       (lp-resize-view
        view-table (lp-resize-keym1 key))
     t))
     (let ((location
            (lp-resize-loc-fn-apply
             loc-function
             (lp-resize-keym1 key))))
       (and
        (integerp location)
        (<= 0 location)
        (< location (len xs))
        (lp-resize-eq-p
         (lp-resize-nth location xs)
         key)
        (lp-resize-valid-probe-path-p
         xs key location))))))

(defun lp-resize-valid-p
    (xs view-table loc-function)
  (and
   (not
    (equal
     (lp-resize-view
      view-table
      (lp-resize-keym1 (lp-resize-dummy)))
     t))
   (lp-resize-valid-data-indices-p
    xs view-table loc-function)
   (lp-resize-valid-view-keys-p
    xs view-table loc-function)))

(defun lp-resize-state-invariant-p (table)
  (and
   (<= 0 (lp-resize-size table))
   (< (lp-resize-size table)
      (len (lp-resize-data table)))
   (equal
    (+ (lp-resize-size table)
       (lp-resize-numof
        (lp-resize-data table)
        0
        (len (lp-resize-data table))))
    (len (lp-resize-data table)))
   (lp-resize-valid-p
    (lp-resize-data table)
    table
    (lp-resize-loc-map table))))

(defun-sk lp-resize-carrier-and-closure-laws-p ()
  (forall (key modeled-key table)
    (and
     (implies
      (lp-resize-key-p key)
      (and
       (lp-resize-keym-p (lp-resize-keym1 key))
       (integerp (lp-resize-hash key))))
     (implies
      (and
       (lp-resize-state-p table)
       (lp-resize-keym-p modeled-key))
      (and
       (booleanp
        (lp-resize-view table modeled-key))
       (integerp
        (lp-resize-loc table modeled-key))))
     (implies
      (lp-resize-state-p table)
      (and
       (lp-resize-loc-fn-p
        (lp-resize-loc-map table))
       (integerp (lp-resize-size table))
       (lp-resize-key-list-p
        (lp-resize-data table)))))))

(defun-sk lp-resize-hash-laws-p ()
  (forall (x y)
    (and
     (implies
      (lp-resize-key-p x)
      (<= 0 (lp-resize-hash x)))
     (implies
      (and
       (lp-resize-key-p x)
       (lp-resize-key-p y)
       (lp-resize-eq-p x y))
      (equal
       (lp-resize-hash x)
       (lp-resize-hash y))))))

(defun-sk lp-resize-all-state-invariants-p ()
  (forall (table)
    (implies
     (lp-resize-state-p table)
     (lp-resize-state-invariant-p table))))

(defun-sk lp-resize-state-injectivity-p ()
  (forall (left right)
    (implies
     (and
      (lp-resize-state-p left)
      (lp-resize-state-p right)
      (equal
       (lp-resize-size left)
       (lp-resize-size right))
      (equal
       (lp-resize-data left)
       (lp-resize-data right))
      (lp-resize-view-equal-p left right)
      (lp-resize-loc-equal-p left right))
     (equal left right))))

(defun lp-resize-source-context-p ()
  (and
   (lp-resize-key-p (lp-resize-key-default))
   (lp-resize-keym-p (lp-resize-keym-default))
   (lp-resize-state-p (lp-resize-state-default))
   (lp-resize-key-p (lp-resize-dummy))
   (lp-resize-loc-fn-p
    (lp-resize-loc-fn-zero))
   (lp-resize-loc-function-laws-p)
   (lp-resize-carrier-and-closure-laws-p)
   (lp-resize-hash-laws-p)
   (lp-resize-all-state-invariants-p)
   (lp-resize-state-injectivity-p)))

;; These predicates are the quantified data and probing clauses of the loop
;; invariant at a given reinsertion threshold.

(defun-sk lp-resize-reinserted-data-p
    (xs original loc-function n2)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index n2)
      (lp-resize-neq-p
       (lp-resize-nth index xs)
       (lp-resize-dummy)))
     (and
      (equal
       (lp-resize-view
        original
        (lp-resize-keym1
         (lp-resize-nth index xs)))
      t)
      (equal
       (lp-resize-loc-fn-apply
        loc-function
        (lp-resize-keym1
         (lp-resize-nth index xs)))
       index)))))

(defun-sk lp-resize-no-key-in-range-p
    (xs key n2)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index n2))
     (lp-resize-neq-p
      (lp-resize-nth index xs)
      key))))

(defun-sk lp-resize-reinserted-view-keys-p
    (xs original loc-function threshold n2)
  (forall (key)
    (implies
     (and
      (lp-resize-key-p key)
      (equal
       (lp-resize-view
        original (lp-resize-keym1 key))
       t))
     (if (<
          (lp-resize-loc
           original (lp-resize-keym1 key))
         threshold)
         (let ((location
                (lp-resize-loc-fn-apply
                 loc-function
                 (lp-resize-keym1 key))))
           (and
            (<= 0 location)
            (< location n2)
            (lp-resize-eq-p
             (lp-resize-nth location xs)
             key)
            (lp-resize-valid-probe-path-p
             xs key location)))
       (lp-resize-no-key-in-range-p
        xs key n2)))))

(defun lp-resize-loop-invariant-p
    (xs original loc-function threshold n2)
  (and
   (equal
    (lp-resize-numof xs 0 n2)
    (+
     (lp-resize-numof
      (lp-resize-data original)
      0 threshold)
     (- n2 threshold)))
   (lp-resize-reinserted-data-p
    xs original loc-function n2)
   (lp-resize-reinserted-view-keys-p
    xs original loc-function threshold n2)))

;; This is extensional equality of the two integer-indexed functions in the
;; source List.set branch.

(defun-sk lp-resize-set-function-equality-p
    (old index value)
  (forall (argument)
    (implies
     (and
      (integerp argument)
      (<= 0 argument)
      (< argument (len old)))
     (equal
      (lp-resize-nth
       argument
       (lp-resize-set old index value))
      (if (equal argument index)
          value
        (lp-resize-nth argument old))))))

(defun-sk lp-resize-no-conflict-before-p
    (key xs stop)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (len xs))
      (lp-resize-between-p
       (lp-resize-bucket key (len xs))
       index
       stop))
     (and
      (lp-resize-neq-p
       (lp-resize-nth index xs)
       key)
      (lp-resize-neq-p
       (lp-resize-nth index xs)
       (lp-resize-dummy))))))

;; This is the postcondition for one selected probe position in the branch
;; where the current original-table entry is non-dummy.

(defun lp-resize-selected-position-result-p
    (original xs loc-function index key position n2)
  (let ((updated
         (lp-resize-set xs position key)))
    (and
     (<= 0 position)
     (< position (len xs))
     (implies
      (equal (len updated) (len xs))
      (implies
       (lp-resize-set-function-equality-p
        xs position key)
       (lp-resize-loop-invariant-p
        updated original
        (lp-resize-loc-fn-update
         loc-function
         (lp-resize-keym1 key)
         position)
        (+ index 1) n2))))))

(defun-sk lp-resize-all-selected-positions-p
    (original xs loc-function index key n2)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (and
       (<= 0 position)
       (< position (len xs))
       (or
        (lp-resize-eq-p
         (lp-resize-nth position xs)
         (lp-resize-dummy))
        (lp-resize-eq-p
         (lp-resize-nth position xs)
         key))
       (lp-resize-no-conflict-before-p
        key xs position))
      (lp-resize-selected-position-result-p
       original xs loc-function index key position n2)))))

(defun lp-resize-loop-step-p
    (original xs loc-function index n2)
  (let* ((key
          (lp-resize-nth
           index (lp-resize-data original)))
         (dummy (lp-resize-dummy)))
    (and
     (<= 0 index)
     (< index (len (lp-resize-data original)))
     (implies
      (iff
       (lp-resize-neq-p key dummy)
       (not
        (equal
         (lp-resize-keym1 key)
         (lp-resize-keym1 dummy))))
      (if (lp-resize-neq-p key dummy)
          (and
           (lp-resize-neq-p key dummy)
           (< 0 (len xs))
           (< 0
              (lp-resize-numof
               xs 0 (len xs)))
           (lp-resize-all-selected-positions-p
            original xs loc-function index key n2))
        (lp-resize-loop-invariant-p
         xs original
         loc-function
         (+ index 1) n2))))))

(defun-sk lp-resize-all-loop-steps-p
    (original xs loc-function lower upper n2)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (<= index upper)
       (lp-resize-loop-invariant-p
        xs original
        loc-function
        index n2))
      (lp-resize-loop-step-p
       original xs loc-function index n2)))))

;; The h1 clauses preserve the exact source conjunction: the reconstructed
;; fields satisfy the invariant formulas, and matching all four fields implies
;; that the resulting state's data length is twice the original length.

(defun lp-resize-state-construction-p
    (xs original loc-function result)
  (and
   (and
    (<= 0 (lp-resize-size original))
    (< (lp-resize-size original)
       (len xs)))
   (equal
    (+ (lp-resize-size original)
       (lp-resize-numof xs 0 (len xs)))
    (len xs))
   (lp-resize-valid-p
    xs original loc-function)
   (implies
    (and
     (equal
      loc-function
      (lp-resize-loc-map result))
     (lp-resize-view-equal-p
      original result)
     (equal xs (lp-resize-data result))
     (equal
      (lp-resize-size original)
      (lp-resize-size result)))
    (equal
     (len (lp-resize-data result))
     (* 2
        (len (lp-resize-data original)))))))

(defun-sk lp-resize-all-state-constructions-p
    (xs original loc-function)
  (forall (result)
    (implies
     (lp-resize-state-p result)
     (lp-resize-state-construction-p
      xs original loc-function result))))

(defun-sk lp-resize-all-reinsertions-p
    (initial original upper n2)
  (forall (loc-function xs)
    (implies
     (and
      (lp-resize-loc-fn-p loc-function)
      (lp-resize-key-list-p xs)
      (equal (len xs) (len initial)))
     (and
      (lp-resize-all-loop-steps-p
       original xs loc-function 0 upper n2)
      (implies
       (lp-resize-loop-invariant-p
        xs original
        loc-function
        (+ upper 1) n2)
       (lp-resize-all-state-constructions-p
        xs original loc-function))))))

(defun-sk lp-resize-all-initial-dummy-p (xs n2)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index n2))
     (equal
      (lp-resize-nth index xs)
      (lp-resize-dummy)))))

(defun lp-resize-initialized-table-obligation-p
    (initial original n n2)
  (let ((upper (- n 1)))
    (and
     (implies
      (<= 0 (+ upper 1))
      (and
       (lp-resize-loop-invariant-p
        initial original
        (lp-resize-loc-fn-zero)
        0 n2)
       (lp-resize-all-reinsertions-p
        initial original upper n2)))
     (implies
      (< (+ upper 1) 0)
      (lp-resize-all-state-constructions-p
       initial original
       (lp-resize-loc-fn-zero))))))

(defun-sk lp-resize-all-candidate-tables-p
    (original n n2)
  (forall (initial)
    (implies
     (and
      (lp-resize-key-list-p initial)
      (lp-resize-all-initial-dummy-p initial n2)
      (equal (len initial) n2))
     (lp-resize-initialized-table-obligation-p
      initial original n n2))))

;; This closed predicate is the complete unproved resize'vc proposition.

(defun-sk ntp4vc-linear-probing-resizeqtvc-statement ()
  (forall (original)
    (implies
     (and
      (lp-resize-source-context-p)
      (lp-resize-state-p original))
     (let* ((n
             (len (lp-resize-data original)))
            (n2 (* 2 n)))
       (and
        (<= 0 n2)
        (lp-resize-all-candidate-tables-p
         original n n2))))))

(value-triple :itpeval-statement-checked)
:q
