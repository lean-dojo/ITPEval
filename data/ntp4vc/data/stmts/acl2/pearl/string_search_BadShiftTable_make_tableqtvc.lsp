;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/string_search_BadShiftTable_make_tableqtvc: the verification
;; condition for constructing a bad-character shift table from a string,
;; preserving its finite-map and mismatch invariants. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Signed integers in the two's-complement 63-bit range represent source
;; bitvectors exactly because the VC observes every such word only through
;; its signed value.

(defconst *bst-min-int63* -4611686018427387904)
(defconst *bst-max-int63* 4611686018427387903)

(defun bst-int63-p (value)
  (and
   (integerp value)
   (<= *bst-min-int63* value)
   (<= value *bst-max-int63*)))

;; Why3 characters are represented by their exact 8-bit integer codes, and
;; strings by finite lists of those codes.

(defun bst-char-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun bst-string-p (value)
  (if (consp value)
      (and
       (bst-char-p (car value))
       (bst-string-p (cdr value)))
    (equal value nil)))

(defun bst-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun bst-string-index (pattern index)
  (let ((natural-index
         (bst-int-to-nat index)))
    (if (< natural-index (len pattern))
        (nth natural-index pattern)
      0)))

;; A finite map is a canonical ascending association list of character keys
;; and signed-63 values. Canonical ordering makes ACL2 equality coincide with
;; source finite-map extensional equality.

(defun bst-fmap-entry-p (entry)
  (and
   (consp entry)
   (bst-char-p (car entry))
   (bst-int63-p (cdr entry))))

(defun bst-fmap-tail-p (lower-key entries)
  (declare (xargs :measure (acl2-count entries)))
  (if (consp entries)
      (and
       (bst-fmap-entry-p (car entries))
       (< lower-key (caar entries))
       (bst-fmap-tail-p
        (caar entries)
        (cdr entries)))
    (equal entries nil)))

(defun bst-fmap-p (map)
  (if (consp map)
      (and
       (bst-fmap-entry-p (car map))
       (bst-fmap-tail-p
        (caar map)
        (cdr map)))
    (equal map nil)))

(defun bst-fmap-member-p (key map)
  (if (assoc-equal key map) t nil))

(defun bst-fmap-lookup (key map)
  (let ((entry (assoc-equal key map)))
    (if entry
        (cdr entry)
      0)))

(defun bst-fmap-insert (key value map)
  (declare (xargs :measure (acl2-count map)))
  (if (consp map)
      (let ((current-key (caar map)))
        (cond
         ((equal key current-key)
          (cons
           (cons key value)
           (cdr map)))
         ((< key current-key)
          (cons
           (cons key value)
           map))
         (t
          (cons
           (car map)
           (bst-fmap-insert
            key value (cdr map))))))
    (list (cons key value))))

;; The source map implementation type remains abstract. Its only observation
;; in this VC is TO_FMAP, whose typing and inhabited domain are explicit.

(defstub bst-table-p (table) t)
(defstub bst-to-fmap (table) t)

(defun-sk bst-table-domain-nonempty-p ()
  (exists (table)
    (bst-table-p table)))

(defun-sk bst-to-fmap-typed-p ()
  (forall (table)
    (implies
     (bst-table-p table)
     (bst-fmap-p
      (bst-to-fmap table)))))

(defun bst-interface-p ()
  (and
   (bst-table-domain-nonempty-p)
   (bst-to-fmap-typed-p)))

;; Loop and record invariants from BadShiftTable.make_table.

(defun-sk bst-prefix-present-p
    (pattern upper table)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper))
      (bst-fmap-member-p
       (bst-string-index pattern index)
       (bst-to-fmap table))))))

(defun-sk bst-values-bounded-p
    (table upper-bound)
  (forall (ch)
    (implies
     (bst-char-p ch)
     (implies
      (bst-fmap-member-p
       ch
       (bst-to-fmap table))
      (and
       (<= 1
           (bst-fmap-lookup
            ch
            (bst-to-fmap table)))
       (<= (bst-fmap-lookup
            ch
            (bst-to-fmap table))
           upper-bound))))))

(defun-sk bst-no-recent-match-p
    (pattern pattern-length table upper)
  (forall (ch index)
    (implies
     (and
      (bst-char-p ch)
      (integerp index)
      (bst-fmap-member-p
       ch
       (bst-to-fmap table))
      (< (- pattern-length
            (bst-fmap-lookup
             ch
             (bst-to-fmap table)))
         index)
      (< index upper))
     (not
      (equal
       (bst-string-index pattern index)
       ch)))))

(defun-sk bst-no-earlier-suffix-match-p
    (pattern table)
  (forall (ch shift)
    (implies
     (and
      (bst-char-p ch)
      (integerp shift)
      (bst-fmap-member-p
       ch
       (bst-to-fmap table))
      (<= 1 shift)
      (< shift
         (bst-fmap-lookup
          ch
          (bst-to-fmap table))))
     (not
      (equal
       (bst-string-index
        pattern
        (- (len pattern) shift))
       ch)))))

(defun bst-complete-invariant-p
    (pattern table)
  (and
   (bst-prefix-present-p
    pattern (len pattern) table)
   (bst-values-bounded-p
    table (+ (len pattern) 1))
   (bst-no-earlier-suffix-match-p
    pattern table)))

(defun bst-loop-state-p
    (pattern pattern-length o1 table index)
  (and
   (<= 0 index)
   (<= index o1)
   (bst-prefix-present-p
    pattern index table)
   (bst-values-bounded-p
    table (+ pattern-length 1))
   (bst-no-recent-match-p
    pattern pattern-length table index)))

(defun-sk bst-all-updated-tables-p
    (pattern pattern-length table index value)
  (forall (updated-table)
    (implies
     (bst-table-p updated-table)
     (implies
      (equal
       (bst-to-fmap updated-table)
       (bst-fmap-insert
        (bst-string-index pattern index)
        value
        (bst-to-fmap table)))
      (and
       (bst-prefix-present-p
        pattern (+ index 1) updated-table)
       (bst-values-bounded-p
        updated-table (+ pattern-length 1))
       (bst-no-recent-match-p
        pattern pattern-length
        updated-table (+ index 1)))))))

(defun bst-o2-body-p
    (pattern pattern-length table index o2)
  (implies
   (equal o2
          (- pattern-length index))
   (and
    (<= 0 index)
    (< index (len pattern))
    (bst-all-updated-tables-p
     pattern pattern-length
     table index o2))))

(defun-sk bst-all-o2-p
    (pattern pattern-length table index)
  (forall (o2)
    (implies
     (bst-int63-p o2)
     (bst-o2-body-p
      pattern pattern-length
      table index o2))))

(defun bst-loop-step-p
    (pattern pattern-length o1 table index)
  (implies
   (bst-loop-state-p
    pattern pattern-length
    o1 table index)
   (and
    (bst-int63-p
     (- pattern-length index))
    (bst-all-o2-p
     pattern pattern-length
     table index))))

(defun-sk bst-all-loop-indices-p
    (pattern pattern-length o1 table)
  (forall (index)
    (implies
     (bst-int63-p index)
     (bst-loop-step-p
      pattern pattern-length
      o1 table index))))

(defun bst-loop-exit-state-p
    (pattern pattern-length o1 table)
  (and
   (bst-prefix-present-p
    pattern (+ o1 1) table)
   (bst-values-bounded-p
    table (+ pattern-length 1))
   (bst-no-recent-match-p
    pattern pattern-length
    table (+ o1 1))))

(defun bst-table-continuation-p
    (pattern pattern-length o1 table)
  (and
   (bst-all-loop-indices-p
    pattern pattern-length o1 table)
   (implies
    (bst-loop-exit-state-p
     pattern pattern-length o1 table)
    (bst-complete-invariant-p
     pattern table))))

(defun-sk bst-all-loop-tables-p
    (pattern pattern-length o1)
  (forall (table)
    (implies
     (bst-table-p table)
     (bst-table-continuation-p
      pattern pattern-length
      o1 table))))

(defun bst-initial-loop-state-p
    (pattern pattern-length table)
  (and
   (bst-prefix-present-p
    pattern 0 table)
   (bst-values-bounded-p
    table (+ pattern-length 1))
   (bst-no-recent-match-p
    pattern pattern-length table 0)))

(defun bst-o1-body-p
    (pattern pattern-length initial-table o1)
  (implies
   (equal o1
          (- pattern-length 1))
   (and
    (implies
     (<= 0 (+ o1 1))
     (and
      (bst-initial-loop-state-p
       pattern pattern-length
       initial-table)
      (bst-all-loop-tables-p
       pattern pattern-length o1)))
    (implies
     (< (+ o1 1) 0)
     (bst-complete-invariant-p
      pattern initial-table)))))

(defun-sk bst-all-o1-p
    (pattern pattern-length initial-table)
  (forall (o1)
    (implies
     (bst-int63-p o1)
     (bst-o1-body-p
      pattern pattern-length
      initial-table o1))))

(defun
    ntp4vc-pearl-string-search-badshifttable-make-tableqtvc-statement
    (m pattern initial-table)
  (implies
   (and
    (bst-interface-p)
    (bst-int63-p m)
    (bst-string-p pattern)
    (bst-table-p initial-table)
    (equal m (len pattern))
    (<= 0 (len pattern))
    (equal
     (bst-to-fmap initial-table)
     nil))
   (and
    (bst-int63-p (- m 1))
    (bst-all-o1-p
     pattern m initial-table))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
