;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/linear_probing_LinearProbing_removeqtvc: the verification condition
;; for removing a key from a linear-probing hash table, establishing the
;; initial deletion hole and the updated abstract view. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These predicates relativize ACL2's universe to the source's arbitrary key,
;; modeled-key, and table-state types. They do not bound or enumerate a
;; carrier. The internally quantified KEYM -> INT location function is
;; eliminated below by an equivalent canonical function induced by H_DATA.

(defstub lp-remove-key-p (x) t)
(defstub lp-remove-keym-p (x) t)
(defstub lp-remove-state-p (x) t)

(defstub lp-remove-key-default () t)
(defstub lp-remove-keym-default () t)
(defstub lp-remove-state-default () t)
(defstub lp-remove-keym1 (key) t)
(defstub lp-remove-hash (key) t)
(defstub lp-remove-dummy () t)
(defstub lp-remove-size (table) t)
(defstub lp-remove-data (table) t)
(defstub lp-remove-view (table modeled-key) t)
(defstub lp-remove-loc (table modeled-key) t)

(defun lp-remove-key-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (lp-remove-key-p (car xs))
       (lp-remove-key-list-p (cdr xs)))
    (equal xs nil)))

;; Equality and disequality are definitionally equality and disequality of the
;; modeled keys, exactly as specified by eq'spec and neq'spec.

(defun lp-remove-eq-p (x y)
  (equal
   (lp-remove-keym1 x)
   (lp-remove-keym1 y)))

(defun lp-remove-neq-p (x y)
  (not (lp-remove-eq-p x y)))

;; INT.TONAT sends negative integers to zero. Source list lookup returns the
;; inhabited key default when that natural index is outside the list.

(defun lp-remove-nth (index xs)
  (if (< (nfix index) (len xs))
      (nth (nfix index) xs)
    (lp-remove-key-default)))

;; This is source List.set: an out-of-range update leaves the list unchanged.

(defun lp-remove-set-nat (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (lp-remove-set-nat
        (cdr xs)
        (- index 1)
        value)))))

(defun lp-remove-set (xs index value)
  (lp-remove-set-nat xs (nfix index) value))

(defun lp-remove-between-p (left point right)
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

(defun lp-remove-next (n index)
  (let ((next-index (+ index 1)))
    (if (equal next-index n)
        0
      next-index)))

;; HASH is nonnegative in the source context. For positive N, ACL2 MOD is
;; therefore the same remainder specified by the three ground-truth files.

(defun lp-remove-bucket (key n)
  (if (and
       (integerp n)
       (< 0 n))
      (mod (lp-remove-hash key) n)
    0))

;; This recursion is the source NumOf.numof recurrence on [LOWER, UPPER).

(defun lp-remove-numof-loop (xs index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
      (lp-remove-eq-p
       (lp-remove-nth index xs)
       (lp-remove-dummy))
      1
      0)
     (lp-remove-numof-loop
      xs
      (+ index 1)
      (- remaining 1)))))

(defun lp-remove-numof (xs lower upper)
  (if (and
       (integerp lower)
       (integerp upper))
      (lp-remove-numof-loop
       xs
       lower
       (nfix (- upper lower)))
    0))

(defun lp-remove-updated-view
    (table removed-key modeled-key)
  (if (equal
       modeled-key
       (lp-remove-keym1 removed-key))
      nil
    (lp-remove-view table modeled-key)))

(defun-sk lp-remove-view-equal-p (left right)
  (forall (modeled-key)
    (implies
     (lp-remove-keym-p modeled-key)
     (equal
      (lp-remove-view left modeled-key)
      (lp-remove-view right modeled-key)))))

(defun-sk lp-remove-loc-equal-p (left right)
  (forall (modeled-key)
    (implies
     (lp-remove-keym-p modeled-key)
     (equal
      (lp-remove-loc left modeled-key)
      (lp-remove-loc right modeled-key)))))

(defun-sk lp-remove-view-update-equal-state-p
    (table removed-key result-table)
  (forall (modeled-key)
    (implies
     (lp-remove-keym-p modeled-key)
     (equal
      (lp-remove-updated-view
       table removed-key modeled-key)
      (lp-remove-view
       result-table modeled-key)))))

(defun-sk lp-remove-valid-data-indices-p (xs table)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (let ((key (lp-remove-nth index xs)))
        (implies
         (lp-remove-neq-p
          key (lp-remove-dummy))
         (and
          (equal
           (lp-remove-view
            table (lp-remove-keym1 key))
           t)
          (equal
           (lp-remove-loc
            table (lp-remove-keym1 key))
           index))))))))

(defun-sk lp-remove-valid-probe-path-p
    (xs key location)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (implies
       (lp-remove-between-p
        (lp-remove-bucket key (len xs))
        index
        location)
       (and
        (lp-remove-neq-p
         (lp-remove-nth index xs)
         key)
        (lp-remove-neq-p
         (lp-remove-nth index xs)
         (lp-remove-dummy))))))))

(defun-sk lp-remove-valid-view-keys-p (xs table)
  (forall (key)
    (implies
     (lp-remove-key-p key)
     (implies
      (equal
       (lp-remove-view
        table (lp-remove-keym1 key))
       t)
      (let ((location
             (lp-remove-loc
              table (lp-remove-keym1 key))))
        (and
         (<= 0 location)
         (< location (len xs))
         (lp-remove-eq-p
          (lp-remove-nth location xs)
          key)
         (lp-remove-valid-probe-path-p
          xs key location)))))))

(defun lp-remove-valid-p (xs table)
  (and
   (not
    (equal
     (lp-remove-view
      table
      (lp-remove-keym1
       (lp-remove-dummy)))
     t))
   (lp-remove-valid-data-indices-p xs table)
   (lp-remove-valid-view-keys-p xs table)))

(defun lp-remove-state-invariant-p (table)
  (and
   (<= 0 (lp-remove-size table))
   (< (lp-remove-size table)
      (len (lp-remove-data table)))
   (equal
    (+ (lp-remove-size table)
       (lp-remove-numof
        (lp-remove-data table)
        0
        (len (lp-remove-data table))))
    (len (lp-remove-data table)))
   (lp-remove-valid-p
    (lp-remove-data table)
    table)))

(defun-sk lp-remove-carrier-and-closure-laws-p ()
  (forall (key modeled-key table)
    (and
     (implies
      (lp-remove-key-p key)
      (and
       (lp-remove-keym-p
        (lp-remove-keym1 key))
       (integerp (lp-remove-hash key))
       (<= 0 (lp-remove-hash key))))
     (implies
      (and
       (lp-remove-state-p table)
       (lp-remove-keym-p modeled-key))
      (and
       (booleanp
        (lp-remove-view table modeled-key))
       (integerp
        (lp-remove-loc table modeled-key))))
     (implies
      (lp-remove-state-p table)
      (and
       (integerp (lp-remove-size table))
       (lp-remove-key-list-p
        (lp-remove-data table)))))))

(defun-sk lp-remove-hash-equality-law-p ()
  (forall (x y)
    (implies
     (and
      (lp-remove-key-p x)
      (lp-remove-key-p y)
      (lp-remove-eq-p x y))
     (equal
      (lp-remove-hash x)
      (lp-remove-hash y)))))

(defun-sk lp-remove-all-state-invariants-p ()
  (forall (table)
    (implies
     (lp-remove-state-p table)
     (lp-remove-state-invariant-p table))))

(defun-sk lp-remove-state-injectivity-p ()
  (forall (left right)
    (implies
     (and
      (lp-remove-state-p left)
      (lp-remove-state-p right)
      (equal
       (lp-remove-size left)
       (lp-remove-size right))
      (equal
       (lp-remove-data left)
       (lp-remove-data right))
      (lp-remove-view-equal-p left right)
      (lp-remove-loc-equal-p left right))
     (equal left right))))

(defun lp-remove-source-context-p ()
  (and
   (lp-remove-key-p (lp-remove-key-default))
   (lp-remove-keym-p (lp-remove-keym-default))
   (lp-remove-state-p (lp-remove-state-default))
   (lp-remove-key-p (lp-remove-dummy))
   (lp-remove-carrier-and-closure-laws-p)
   (lp-remove-hash-equality-law-p)
   (lp-remove-all-state-invariants-p)
   (lp-remove-state-injectivity-p)))

;; This is the universal condition excluding X and DUMMY before the selected
;; circular probe position.

(defun-sk lp-remove-no-conflict-before-p
    (removed-key xs stop)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (implies
       (lp-remove-between-p
        (lp-remove-bucket
         removed-key (len xs))
        index
        stop)
       (and
        (lp-remove-neq-p
         (lp-remove-nth index xs)
         removed-key)
        (lp-remove-neq-p
         (lp-remove-nth index xs)
         (lp-remove-dummy))))))))

;; The source array update is observed only at valid array indices.  Keeping
;; that domain explicit avoids conflating negative integer indices with slot
;; zero in this list-backed encoding.

(defun-sk lp-remove-set-function-equality-p
    (old index value)
  (forall (argument)
    (implies
     (and
      (integerp argument)
      (<= 0 argument)
      (< argument (len old)))
     (equal
      (lp-remove-nth
       argument
       (lp-remove-set old index value))
      (if (equal argument index)
          value
        (lp-remove-nth argument old))))))

(defun-sk lp-remove-no-dummy-between-p
    (xs start finish excluded)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (implies
       (lp-remove-between-p
        start index finish)
       (implies
        (not (equal index excluded))
        (lp-remove-neq-p
         (lp-remove-nth index xs)
         (lp-remove-dummy))))))))

(defun-sk lp-remove-updated-data-indices-p
    (removed-key table hole xs)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (let ((key (lp-remove-nth index xs)))
        (implies
         (lp-remove-neq-p
          key (lp-remove-dummy))
         (and
          (equal
           (lp-remove-updated-view
            table removed-key
            (lp-remove-keym1 key))
           t)
          (equal
           (lp-remove-loc
            table (lp-remove-keym1 key))
           index))))))))

(defun-sk lp-remove-updated-probe-path-p
    (key location hole xs)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (implies
       (lp-remove-between-p
        (lp-remove-bucket key (len xs))
        index
        location)
       (and
        (lp-remove-neq-p
         (lp-remove-nth index xs)
         key)
        (or
         (lp-remove-neq-p
          (lp-remove-nth index xs)
          (lp-remove-dummy))
         (and
          (equal index hole)
          (lp-remove-between-p
           hole hole location)))))))))

(defun-sk lp-remove-updated-view-keys-p
    (removed-key table hole xs)
  (forall (key)
    (implies
     (lp-remove-key-p key)
     (implies
      (equal
       (lp-remove-updated-view
        table removed-key
        (lp-remove-keym1 key))
       t)
      (let ((location
             (lp-remove-loc
              table (lp-remove-keym1 key))))
        (and
         (<= 0 location)
         (< location (len xs))
         (lp-remove-eq-p
          (lp-remove-nth location xs)
          key)
         (lp-remove-updated-probe-path-p
          key location hole xs)))))))

(defun lp-remove-updated-map-obligation-p
    (removed-key table hole xs)
  (and
   (not
    (equal
     (lp-remove-updated-view
      table removed-key
      (lp-remove-keym1
       (lp-remove-dummy)))
     t))
   (lp-remove-updated-data-indices-p
    removed-key table hole xs)
   (lp-remove-updated-view-keys-p
    removed-key table hole xs)))

(defun lp-remove-canonical-loc-aux
    (modeled-key xs index)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      0
    (if (equal
         (lp-remove-keym1 (car xs))
         modeled-key)
        index
      (lp-remove-canonical-loc-aux
       modeled-key
       (cdr xs)
       (+ index 1)))))

(defun lp-remove-canonical-loc (modeled-key xs)
  (lp-remove-canonical-loc-aux
   modeled-key xs 0))

;; In VALID, every non-dummy data entry requires L(KEYM1 entry) to equal its
;; index. Hence any valid L agrees, on every relevant modeled key, with the
;; first-occurrence location below; duplicate relevant entries would make
;; VALID false. Conversely this total integer-valued canonical location
;; supplies an L whenever these canonical VALID clauses hold. Thus replacing
;; the function quantifier by canonical validity is bidirectionally exact.

(defun-sk lp-remove-canonical-valid-data-indices-p
    (xs removed-key table)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (let ((key (lp-remove-nth index xs)))
        (implies
         (lp-remove-neq-p
          key (lp-remove-dummy))
         (and
          (equal
           (lp-remove-updated-view
            table removed-key
            (lp-remove-keym1 key))
           t)
          (equal
           (lp-remove-canonical-loc
            (lp-remove-keym1 key)
            xs)
           index))))))))

(defun-sk lp-remove-canonical-valid-view-keys-p
    (xs removed-key table)
  (forall (key)
    (implies
     (lp-remove-key-p key)
     (implies
      (equal
       (lp-remove-updated-view
        table removed-key
        (lp-remove-keym1 key))
       t)
      (let ((location
             (lp-remove-canonical-loc
              (lp-remove-keym1 key)
              xs)))
        (and
         (<= 0 location)
         (< location (len xs))
         (lp-remove-eq-p
          (lp-remove-nth location xs)
          key)
         (lp-remove-valid-probe-path-p
          xs key location)))))))

(defun lp-remove-canonical-valid-p
    (xs removed-key table)
  (and
   (not
    (equal
     (lp-remove-updated-view
      table removed-key
      (lp-remove-keym1
       (lp-remove-dummy)))
     t))
   (lp-remove-canonical-valid-data-indices-p
    xs removed-key table)
   (lp-remove-canonical-valid-view-keys-p
    xs removed-key table)))

(defun lp-remove-constructed-invariant-p
    (removed-key table xs)
  (and
   (and
    (<= 0 (- (lp-remove-size table) 1))
    (< (- (lp-remove-size table) 1)
       (len xs)))
   (equal
    (+ (- (lp-remove-size table) 1)
       (lp-remove-numof xs 0 (len xs)))
    (len xs))
   (lp-remove-canonical-valid-p
    xs removed-key table)))

;; The source's remaining universal result-state clause has the invariant
;; above as its state-independent conjunct. Its other conjunct is A -> A,
;; since its antecedent already contains the conclusion's view equality.
;; The inhabited state carrier therefore makes that universal clause exactly
;; equivalent to this invariant, without weakening the bounds/count demand.

(defun-sk lp-remove-final-state-obligation-p
    (removed-key table updated)
  (forall (xs)
    (implies
     (lp-remove-key-list-p xs)
     (implies
      (equal (len xs) (len updated))
      (implies
       (equal (len xs) (len updated))
       (implies
        (and
         (equal
          (lp-remove-numof xs 0 (len xs))
         (lp-remove-numof
           updated 0 (len xs)))
         (lp-remove-canonical-valid-p
          xs removed-key table))
        (lp-remove-constructed-invariant-p
         removed-key table xs)))))))

(defun lp-remove-hole-result-p
    (removed-key table hole updated finish)
  (and
   (and
    (<= 0 finish)
    (< finish (len updated)))
   (and
    (<= 0 hole)
    (< hole (len updated)))
   (and
    (<= 0 hole)
    (< hole (len updated)))
   (not (equal hole finish))
   (lp-remove-eq-p
    (lp-remove-nth hole updated)
    (lp-remove-dummy))
   (lp-remove-eq-p
    (lp-remove-nth finish updated)
    (lp-remove-dummy))
   (lp-remove-between-p
    hole hole finish)
   (lp-remove-no-dummy-between-p
    updated hole finish hole)
   (lp-remove-updated-map-obligation-p
    removed-key table hole updated)
   (lp-remove-final-state-obligation-p
    removed-key table updated)))

(defun-sk lp-remove-all-hole-results-p
    (removed-key table hole updated)
  (forall (finish)
    (implies
     (integerp finish)
     (implies
      (and
       (and
        (<= 0 finish)
        (< finish (len updated)))
       (not (equal finish hole))
       (lp-remove-eq-p
        (lp-remove-nth finish updated)
        (lp-remove-dummy))
       (lp-remove-no-dummy-between-p
        updated hole finish hole))
      (lp-remove-hole-result-p
       removed-key
       table
       hole
       updated
       finish)))))

(defun lp-remove-after-set-p
    (removed-key table hole updated)
  (let ((next-index
         (lp-remove-next
          (len (lp-remove-data table))
          hole)))
    (and
     (and
      (<= 0 hole)
      (< hole (len updated)))
     (and
      (<= 0 next-index)
      (< next-index (len updated)))
     (not (equal next-index hole))
     (if (<= hole next-index)
         (<=
          1
          (+ (lp-remove-numof
              updated
              next-index
              (len updated))
             (lp-remove-numof
              updated
              0
              hole)))
       (<=
        1
        (lp-remove-numof
         updated next-index hole)))
     (lp-remove-no-dummy-between-p
      updated hole next-index hole)
     (lp-remove-all-hole-results-p
      removed-key table hole updated))))

(defun lp-remove-set-branch-p
    (removed-key table index)
  (let* ((old-data (lp-remove-data table))
         (dummy (lp-remove-dummy))
         (updated
          (lp-remove-set old-data index dummy)))
    (and
     (<= 0 index)
     (< index (len old-data))
     (implies
      (equal
       (len updated)
       (len old-data))
      (implies
       (equal
        (len updated)
        (len (lp-remove-data table)))
       (implies
        (lp-remove-set-function-equality-p
         old-data index dummy)
        (lp-remove-after-set-p
         removed-key
         table
         index
         updated)))))))

(defun lp-remove-probe-result-p
    (removed-key table index)
  (let* ((old-data (lp-remove-data table))
         (old-key (lp-remove-nth index old-data))
         (dummy (lp-remove-dummy)))
    (and
     (<= 0 index)
     (< index (len old-data))
     (implies
      (iff
       (lp-remove-neq-p old-key dummy)
       (not
        (equal
         (lp-remove-keym1 old-key)
         (lp-remove-keym1 dummy))))
      (if (lp-remove-neq-p old-key dummy)
          (lp-remove-set-branch-p
           removed-key table index)
        (lp-remove-view-update-equal-state-p
         table removed-key table))))))

(defun-sk lp-remove-all-probe-results-p
    (removed-key table)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len (lp-remove-data table)))
       (or
        (lp-remove-eq-p
         (lp-remove-nth
          index (lp-remove-data table))
         (lp-remove-dummy))
        (lp-remove-eq-p
         (lp-remove-nth
          index (lp-remove-data table))
         removed-key))
       (lp-remove-no-conflict-before-p
        removed-key
        (lp-remove-data table)
        index))
      (lp-remove-probe-result-p
       removed-key table index)))))

(defun lp-remove-vc-conclusion-p
    (removed-key table)
  (let ((xs (lp-remove-data table)))
    (and
     (lp-remove-neq-p
      removed-key (lp-remove-dummy))
     (and
      (< 0 (len xs))
      (< 0
         (lp-remove-numof xs 0 (len xs))))
     (lp-remove-all-probe-results-p
      removed-key table))))

;; This closed predicate is the complete unproved remove'vc proposition.

(defun-sk ntp4vc-linear-probing-removeqtvc-statement ()
  (forall (removed-key table)
    (implies
     (and
      (lp-remove-source-context-p)
      (lp-remove-key-p removed-key)
      (lp-remove-state-p table)
      (lp-remove-neq-p
       removed-key (lp-remove-dummy)))
     (lp-remove-vc-conclusion-p
      removed-key table))))

(value-triple :itpeval-statement-checked)
:q
