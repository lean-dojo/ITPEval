;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/linear_probing_LinearProbing_memqtvc: the membership verification
;; condition for a linear-probing hash table, relating a terminating probe
;; position to the table's abstract view. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These recognizers relativize ACL2's universe to the source's arbitrary key,
;; key-model, and table-state types.  They do not bound or enumerate a carrier.

(defstub lp-mem-key-p (x) t)
(defstub lp-mem-keym-p (x) t)
(defstub lp-mem-state-p (x) t)

(defstub lp-mem-key-default () t)
(defstub lp-mem-keym-default () t)
(defstub lp-mem-state-default () t)
(defstub lp-mem-keym1 (key) t)
(defstub lp-mem-hash (key) t)
(defstub lp-mem-dummy () t)
(defstub lp-mem-size (table) t)
(defstub lp-mem-data (table) t)
(defstub lp-mem-view (table modeled-key) t)
(defstub lp-mem-loc (table modeled-key) t)

(defun lp-mem-key-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (lp-mem-key-p (car xs))
       (lp-mem-key-list-p (cdr xs)))
    (equal xs nil)))

;; Equality and disequality are definitionally the equality and disequality of
;; the modeled keys, exactly as required by eq'spec and neq'spec.

(defun lp-mem-eq-p (x y)
  (equal
   (lp-mem-keym1 x)
   (lp-mem-keym1 y)))

(defun lp-mem-neq-p (x y)
  (not (lp-mem-eq-p x y)))

;; INT.TONAT sends negative integers to zero.  Source list lookup uses the
;; inhabited key default when that natural index is outside the list.

(defun lp-mem-nth (index xs)
  (if (< (nfix index) (len xs))
      (nth (nfix index) xs)
    (lp-mem-key-default)))

(defun lp-mem-between-p (left point right)
  (or
   (and (<= left point)
        (< point right))
   (and (< right left)
        (<= left point))
   (and (< point right)
        (< right left))))

;; HASH is nonnegative in the source context.  For positive N, ACL2 MOD is
;; exactly the pinned Why3 ComputerDivision.mod operation used by bucket.

(defun lp-mem-bucket (key n)
  (if (and
       (integerp n)
       (< 0 n))
      (mod (lp-mem-hash key) n)
    0))

;; This recursion is the source NumOf.numof recurrence on [LOWER, UPPER).

(defun lp-mem-numof-loop (xs index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
      (lp-mem-eq-p
       (lp-mem-nth index xs)
       (lp-mem-dummy))
      1
      0)
     (lp-mem-numof-loop
      xs
      (+ index 1)
      (- remaining 1)))))

(defun lp-mem-numof (xs lower upper)
  (if (and
       (integerp lower)
       (integerp upper))
      (lp-mem-numof-loop
       xs
       lower
       (nfix (- upper lower)))
    0))

(defun-sk lp-mem-valid-data-indices-p (xs table)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (let ((key (lp-mem-nth index xs)))
        (implies
         (lp-mem-neq-p key (lp-mem-dummy))
         (and
          (equal
           (lp-mem-view table (lp-mem-keym1 key))
           t)
          (equal
           (lp-mem-loc table (lp-mem-keym1 key))
           index))))))))

(defun-sk lp-mem-valid-probe-path-p (xs key location)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (implies
       (lp-mem-between-p
        (lp-mem-bucket key (len xs))
        index
        location)
       (and
        (lp-mem-neq-p
         (lp-mem-nth index xs)
         key)
        (lp-mem-neq-p
         (lp-mem-nth index xs)
         (lp-mem-dummy))))))))

(defun-sk lp-mem-valid-view-keys-p (xs table)
  (forall (key)
    (implies
     (lp-mem-key-p key)
     (implies
      (equal
       (lp-mem-view table (lp-mem-keym1 key))
       t)
      (let ((location
             (lp-mem-loc table (lp-mem-keym1 key))))
        (and
         (<= 0 location)
         (< location (len xs))
         (lp-mem-eq-p
          (lp-mem-nth location xs)
          key)
         (lp-mem-valid-probe-path-p
          xs key location)))))))

(defun lp-mem-valid-p (xs table)
  (and
   (not
    (equal
     (lp-mem-view
      table
      (lp-mem-keym1 (lp-mem-dummy)))
     t))
   (lp-mem-valid-data-indices-p xs table)
   (lp-mem-valid-view-keys-p xs table)))

(defun lp-mem-state-invariant-p (table)
  (and
   (<= 0 (lp-mem-size table))
   (< (lp-mem-size table)
      (len (lp-mem-data table)))
   (equal
    (+ (lp-mem-size table)
       (lp-mem-numof
        (lp-mem-data table)
        0
        (len (lp-mem-data table))))
    (len (lp-mem-data table)))
   (lp-mem-valid-p
    (lp-mem-data table)
    table)))

(defun-sk lp-mem-view-equal-p (left right)
  (forall (modeled-key)
    (implies
     (lp-mem-keym-p modeled-key)
     (equal
      (lp-mem-view left modeled-key)
      (lp-mem-view right modeled-key)))))

(defun-sk lp-mem-loc-equal-p (left right)
  (forall (modeled-key)
    (implies
     (lp-mem-keym-p modeled-key)
     (equal
      (lp-mem-loc left modeled-key)
      (lp-mem-loc right modeled-key)))))

(defun-sk lp-mem-carrier-and-closure-laws-p ()
  (forall (key modeled-key table)
    (and
     (implies
      (lp-mem-key-p key)
      (and
       (lp-mem-keym-p (lp-mem-keym1 key))
       (integerp (lp-mem-hash key))
       (<= 0 (lp-mem-hash key))))
     (implies
      (and
       (lp-mem-state-p table)
       (lp-mem-keym-p modeled-key))
      (and
       (booleanp (lp-mem-view table modeled-key))
       (integerp (lp-mem-loc table modeled-key))))
     (implies
      (lp-mem-state-p table)
      (and
       (integerp (lp-mem-size table))
       (lp-mem-key-list-p
        (lp-mem-data table)))))))

(defun-sk lp-mem-hash-equality-law-p ()
  (forall (x y)
    (implies
     (and
      (lp-mem-key-p x)
      (lp-mem-key-p y)
      (lp-mem-eq-p x y))
     (equal
      (lp-mem-hash x)
      (lp-mem-hash y)))))

(defun-sk lp-mem-all-state-invariants-p ()
  (forall (table)
    (implies
     (lp-mem-state-p table)
     (lp-mem-state-invariant-p table))))

(defun-sk lp-mem-state-injectivity-p ()
  (forall (left right)
    (implies
     (and
      (lp-mem-state-p left)
      (lp-mem-state-p right)
      (equal
       (lp-mem-size left)
       (lp-mem-size right))
      (equal
       (lp-mem-data left)
       (lp-mem-data right))
      (lp-mem-view-equal-p left right)
      (lp-mem-loc-equal-p left right))
     (equal left right))))

(defun lp-mem-source-context-p ()
  (and
   (lp-mem-key-p (lp-mem-key-default))
   (lp-mem-keym-p (lp-mem-keym-default))
   (lp-mem-state-p (lp-mem-state-default))
   (lp-mem-key-p (lp-mem-dummy))
   (lp-mem-carrier-and-closure-laws-p)
   (lp-mem-hash-equality-law-p)
   (lp-mem-all-state-invariants-p)
   (lp-mem-state-injectivity-p)))

;; This is the inner universal condition saying that no earlier circular probe
;; position contains either X or DUMMY.

(defun-sk lp-mem-no-conflict-before-p (x xs stop)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (implies
       (lp-mem-between-p
        (lp-mem-bucket x (len xs))
        index
        stop)
       (and
        (lp-mem-neq-p
         (lp-mem-nth index xs)
         x)
        (lp-mem-neq-p
         (lp-mem-nth index xs)
         (lp-mem-dummy))))))))

(defun lp-mem-probe-result-p (x table index)
  (let* ((xs (lp-mem-data table))
         (old-key (lp-mem-nth index xs))
         (dummy (lp-mem-dummy)))
    (and
     (<= 0 index)
     (< index (len xs))
     (implies
      (iff
       (lp-mem-neq-p old-key dummy)
       (not
        (equal
         (lp-mem-keym1 old-key)
         (lp-mem-keym1 dummy))))
      (iff
       (lp-mem-neq-p old-key dummy)
       (equal
        (lp-mem-view table (lp-mem-keym1 x))
        t))))))

(defun-sk lp-mem-all-probe-results-p (x table)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len (lp-mem-data table)))
       (or
        (lp-mem-eq-p
         (lp-mem-nth index (lp-mem-data table))
         (lp-mem-dummy))
        (lp-mem-eq-p
         (lp-mem-nth index (lp-mem-data table))
         x))
       (lp-mem-no-conflict-before-p
        x
        (lp-mem-data table)
        index))
      (lp-mem-probe-result-p
       x table index)))))

(defun lp-mem-vc-conclusion-p (x table)
  (let ((xs (lp-mem-data table)))
    (and
     (lp-mem-neq-p x (lp-mem-dummy))
     (< 0 (len xs))
     (< 0 (lp-mem-numof xs 0 (len xs)))
     (lp-mem-all-probe-results-p x table))))

;; This closed predicate is the complete unproved mem'vc proposition.

(defun-sk ntp4vc-linear-probing-memqtvc-statement ()
  (forall (x table)
    (implies
     (and
      (lp-mem-source-context-p)
      (lp-mem-key-p x)
      (lp-mem-state-p table)
      (lp-mem-neq-p x (lp-mem-dummy)))
     (lp-mem-vc-conclusion-p x table))))

(value-triple :itpeval-statement-checked)
:q
